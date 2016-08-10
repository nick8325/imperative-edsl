-- A verification engine which uses predicate abstraction to find
-- invariants and an SMT solver to discharge proof obligations.
-- For the algorithm used, see
--   Predicate abstraction for software verification (Flanagan, Qadeer)
-- although the implementation looks very different.

{-# LANGUAGE UndecidableInstances #-}
module Language.Embedded.Verify where

import Prelude hiding (break)
import Data.List hiding (break)
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import Data.Ord
import Data.Typeable
import Data.Constraint(Constraint, Dict(..))
import Control.Monad.RWS.Strict
import Control.Monad.Exception

import Data.ALaCarte
import Language.Embedded.Imperative.CMD hiding (ControlCMD(..))
import Language.Embedded.Expression
import Language.Embedded.Concurrent.CMD
import Language.Embedded.Verify.FirstOrder hiding (Hint)
import qualified Language.Embedded.Verify.FirstOrder as CMD
import qualified Language.Embedded.Verify.Abstract as Abstract
import Control.Monad.Operational.Higher(Program)
import Language.Embedded.Verify.SMT hiding (not, ite, stack, concat)
import qualified Language.Embedded.Verify.SMT as SMT

----------------------------------------------------------------------
-- The verification monad.
----------------------------------------------------------------------

-- Our verification algorithm looks a lot like symbolic execution.
-- The difference is that we use an SMT solver to do the symbolic
-- reasoning.
--
-- We model the state of the program as the state of the SMT solver
-- plus a context, which is a map from variable name to SMT value.
-- Symbolically executing a statement modifies this state to become
-- the state after executing the statement. Typically, this modifies
-- the context (when a variable has changed) or adds new axioms to the
-- SMT solver.
--
-- The verification monad allows us to easily manipulate the SMT
-- solver and the context. It also provides three other features:
--
-- First, it supports branching on the value of a formula, executing
-- one branch if the formula is true and the other if the formula is
-- false. The monad takes care of merging the contexts from the two
-- branches afterwards, as well as making sure that any axiom we add
-- inside a branch is only assumed conditionally.
--
-- Second, it supports break statements in a rudimentary way. We can
-- record when we reach a break statement, and ask the monad for a
-- symbolic expression that tells us whether a given statement breaks.
-- However, skipping past statements after a break is the
-- responsibility of the user of the monad.
--
-- Finally, we can emit warnings during verification, for example when
-- we detect a read of an uninitialised reference.

-- The Verify monad itself is a reader/writer/state monad with the
-- following components:
--
-- Read:  list of formulas which are true in the current branch;
--        "chattiness level" (if > 0 then tracing messages are printed);
--        whether to try to prove anything or just evaluate the program.
-- Write: disjunction which is true if the program has called break;
--        list of warnings generated;
--        list of hints given;
--        list of names generated (must not appear in hints)
-- State: the context, a map from variables to SMT values
type Verify = RWST ([SExpr], Int, Mode) ([SExpr], [String], [HintBody], [String]) Context SMT
data Mode = Prove | Execute deriving Eq

runVerify :: Verify a -> IO (a, [String])
runVerify m = runZ3 ["-t:1000"] $ do
  SMT.setOption ":produce-models" "false"
  (x, (_, warns, _, _)) <- evalRWST m ([], 0, Prove) Map.empty
  return (x, warns)

-- Run a computation without proving anything.
quickly :: Verify a -> Verify a
quickly = local (\(branch, chat, _) -> (branch, chat, Execute))

-- Only run a computation if we are supposed to be proving.
proving :: a -> Verify a -> Verify a
proving def mx = do
  (_, _, mode) <- ask
  case mode of
    Prove   -> mx
    Execute -> return def

-- Assume that a given formula is true.
assume :: String -> SExpr -> Verify ()
assume msg p = proving () $ do
  branch <- branch
  trace msg "Asserted" p
  lift (assert (disj (p:map SMT.not branch)))

-- Check if a given formula holds.
provable :: String -> SExpr -> Verify Bool
provable msg p = proving False $ do
  branch <- branch
  stack $ do
    res <- lift $ do
      mapM_ assert branch
      assert (SMT.not p)
      check
    chat $
      case res of
        Sat -> stack $ do
          trace msg "Failed to prove" p
          lift $ setOption ":produce-models" "true"
          lift $ check
          context <- get
          model   <- showModel context
          liftIO $ putStrLn ("  (countermodel is " ++ model ++ ")")
        Unsat   -> trace msg "Proved" p
        Unknown -> trace msg "Couldn't solve" p
    return (res == Unsat)

-- Print a formula for debugging purposes.
trace :: String -> String -> SExpr -> Verify ()
trace msg kind p = chat $ do
  branch <- branch >>= mapM (lift . simplify)
  p <- lift $ simplify p

  liftIO $ do
    putStr (kind ++ " " ++ showSExpr p ++ " (" ++ msg ++ ")")
    case branch of
      [] -> putStrLn ""
      [x] -> do
        putStrLn (" assuming " ++ showSExpr x)
      _ -> do
        putStrLn " assuming:"
        sequence_ [ putStrLn ("  " ++ showSExpr x) | x <- branch ]

-- Run a computation but undo its effects afterwards.
stack :: Verify a -> Verify a
stack mx = do
  state <- get
  read <- ask
  fmap fst $ lift $ SMT.stack $ evalRWST mx read state

-- Branch on the value of a formula.
ite :: SExpr -> Verify a -> Verify b -> Verify (a, b)
ite p mx my = do
  ctx <- get
  read <- ask
  let
    withBranch p
      | p == bool True  = local id
      | p == bool False = local (\(_,  x, y) -> ([p],  x, y))
      | otherwise       = local (\(xs, x, y) -> (p:xs, x, y))
  (x, ctx1, (break1, warns1, hints1, decls1)) <- lift $ runRWST (withBranch p mx) read ctx
  (y, ctx2, (break2, warns2, hints2, decls2)) <- lift $ runRWST (withBranch (SMT.not p) my) read ctx
  mergeContext p ctx1 ctx2 >>= put
  let
    break
      | null break1 && null break2 = []
      | otherwise = [SMT.ite p (disj break1) (disj break2)]
  tell (break, warns1 ++ warns2, hints1 ++ hints2, decls1 ++ decls2)
  return (x, y)

-- Read the current branch.
branch :: Verify [SExpr]
branch = asks (\(branch, _, _) -> branch)

-- Read the context.
peek :: (Typeable a, Ord a, Mergeable a, Show a, ShowModel a, Invariant a, Exprs a) => String -> Verify a
peek name = do
  ctx <- get
  return (lookupContext name ctx)

-- Write to the context.
poke :: (Typeable a, Ord a, Mergeable a, Show a, ShowModel a, Invariant a, Exprs a) => String -> a -> Verify ()
poke name val = modify (insertContext name val)

-- Record that execution has broken here.
break :: Verify ()
break = do
  branch <- branch
  tell ([conj branch], [], [], [])

-- Check if execution of a statement can break.
withBreaks :: Verify a -> Verify (a, SExpr)
withBreaks mx = do
  (x, (exits, _, _, _)) <- listen mx
  return (x, disj exits)

-- Check if execution of a statement can break, discarding the
-- statement's result.
breaks :: Verify a -> Verify SExpr
breaks mx = fmap snd (withBreaks mx)

-- Prevent a statement from breaking.
noBreak :: Verify a -> Verify a
noBreak = censor (\(_, warns, hints, decls) -> ([], warns, hints, decls))

-- Add a warning to the output.
warn :: String -> Verify ()
warn msg = tell ([], [msg], [], [])

-- Add a hint to the output.
hint :: TypedSExpr a => a -> Verify ()
hint exp = tell ([], [], [HintBody (toSMT exp) (smtType exp)], [])

hintFormula :: SExpr -> Verify ()
hintFormula exp = tell ([], [], [HintBody exp tBool],[])

-- Run a computation but ignoring its warnings.
noWarn :: Verify a -> Verify a
noWarn = censor (\(breaks, _, hints, decls) -> (breaks, [], hints, decls))

-- Run a computation more chattily.
chattily :: Verify a -> Verify a
chattily = local (\(ctx, n, prove) -> (ctx, n+1, prove))

-- Run a computation more quietly.
quietly :: Verify a -> Verify a
quietly = local (\(ctx, n, prove) -> (ctx, n-1, prove))

-- Produce debug output.
chat :: Verify () -> Verify ()
chat mx = do
  (_, chatty, _) <- ask
  when (chatty > 0) mx

----------------------------------------------------------------------
-- The API for verifying programs.
----------------------------------------------------------------------

-- A typeclass for things which can be symbolically executed.
class Verifiable prog where
  -- Returns the transformed program (in which e.g. proved assertions
  -- may have been removed), together with the result.
  verifyWithResult :: prog a -> Verify (prog a, a)

-- Symbolically execute a program, ignoring the result.
verify :: Verifiable prog => prog a -> Verify (prog a)
verify = fmap fst . verifyWithResult

instance (Patch prog, PatchConstraint prog prog, VerifyInstr (FirstOrder prog) exp pred) => Verifiable (Program prog (Param2 exp pred)) where
  verifyWithResult prog = do
    (prog', res) <- verifyWithResult (defunctionalise prog)
    return (patch prog' prog, res)

instance VerifyInstr prog exp pred => Verifiable (Prog prog (Param2 exp pred)) where
  verifyWithResult (Return x)   = return (Return x, x)
  verifyWithResult (Bind x m k) = do
    (m', breaks) <- withBreaks (verifyInstr m x)
    (_, (k', res)) <- ite breaks (return ()) (verifyWithResult k)
    return (Bind x m' k', res)

-- A typeclass for instructions which can be symbolically executed.
class VerifyInstr instr exp pred where
  verifyInstr :: Verifiable prog =>
    instr '(prog, Param2 exp pred) a -> a ->
    Verify (instr '(prog, Param2 exp pred) a)
  verifyInstr instr _ = return instr

instance (VerifyInstr f exp pred, VerifyInstr g exp pred) => VerifyInstr (f :+: g) exp pred where
  verifyInstr (Inl m) x = fmap Inl (verifyInstr m x)
  verifyInstr (Inr m) x = fmap Inr (verifyInstr m x)

----------------------------------------------------------------------
-- Expressions and invariants.
----------------------------------------------------------------------

-- A typeclass for expressions which can be evaluated under a context.
class Typeable exp => SMTEval1 exp where
  -- The result type of evaluating the expression.
  data SMTExpr exp a
  eval :: exp a -> Verify (SMTExpr exp a)

  -- A predicate which must be true of the expression type.
  type Pred exp :: * -> Constraint

  -- Witness the fact that (SMTEval1 exp, Pred exp a) => SMTEval exp a.
  witnessPred :: Pred exp a => exp a -> Dict (SMTEval exp a)

-- A typeclass for expressions of a particular type.
class (SMTEval1 exp, TypedSExpr (SMTExpr exp a), Typeable a) => SMTEval exp a where
  fromConstant :: a -> SMTExpr exp a

  witnessNum :: Num a => exp a -> Dict (Num (SMTExpr exp a))
  witnessNum = error "witnessNum"

  witnessOrd :: Ord a => exp a -> Dict (SMTOrd (SMTExpr exp a))
  witnessOrd = error "witnessOrd"

class Fresh a => TypedSExpr a where
  smtType :: a -> SExpr
  toSMT   :: a -> SExpr
  fromSMT :: SExpr -> a

freshSExpr :: forall a. TypedSExpr a => String -> Verify a
freshSExpr name = fmap fromSMT (freshVar name (smtType (undefined :: a)))

-- A replacement for the SMTOrd class.
class SMTOrd a where
  (.<.), (.<=.), (.>.), (.>=.) :: a -> a -> SExpr

instance SMTEval exp a => Eq (SMTExpr exp a) where
  x == y = toSMT x == toSMT y

instance SMTEval exp a => Ord (SMTExpr exp a) where
  compare = comparing toSMT

instance SMTEval exp a => Show (SMTExpr exp a) where
  showsPrec n x = showsPrec n (toSMT x)

instance SMTEval exp a => Mergeable (SMTExpr exp a) where
  merge cond x y = fromSMT (merge cond (toSMT x) (toSMT y))

instance SMTEval exp a => ShowModel (SMTExpr exp a) where
  showModel x = showModel (toSMT x)

instance SMTEval exp a => Fresh (SMTExpr exp a) where
  fresh name =
    fmap fromSMT (freshVar name (smtType (undefined :: SMTExpr exp a)))

-- A few typed replacements for SMTLib functionality.
(.==.) :: TypedSExpr a => a -> a -> SExpr
x .==. y = toSMT x `eq` toSMT y

smtIte :: TypedSExpr a => SExpr -> a -> a -> a
smtIte cond x y = fromSMT (SMT.ite cond (toSMT x) (toSMT y))

class Fresh a where
  -- Create an uninitialised value.
  -- The String argument is a hint for making pretty names.
  fresh :: String -> Verify a

freshVar name ty = do
  n <- lift freshNum
  let x = name ++ "." ++ show n
  tell ([], [], [], [x])
  lift $ declare x ty

-- A typeclass for values that can undergo predicate abstraction.
class (IsLiteral (Literal a), Fresh a) => Invariant a where
  data Literal a

  -- Forget the value of a binding.
  havoc :: String -> a -> Verify a
  havoc name _ = fresh name

  -- Return a list of candidate literals for a value.
  literals :: String -> a -> [Literal a]
  literals _ _ = []

class (Ord a, Typeable a, Show a) => IsLiteral a where
  -- Evaluate a literal.
  -- The two context arguments are the old and new contexts
  -- (on entry to the loop and now).
  smtLit :: Context -> Context -> a -> SExpr
  smtLit = error "smtLit not defined"

data HintBody =
  HintBody {
    hb_exp  :: SExpr,
    hb_type :: SExpr }
  deriving (Eq, Ord)
instance Show HintBody where show = showSExpr . hb_exp

data Hint =
  Hint {
    hint_ctx  :: Context,
    hint_body :: HintBody }
  deriving (Eq, Ord)
instance Show Hint where show = show . hint_body

instance IsLiteral Hint where
  smtLit _ ctx hint =
    subst (hb_exp (hint_body hint))
    where
      subst x | Just y <- lookup x sub = y
      subst (Atom xs) = Atom xs
      subst (List xs) = List (map subst xs)

      sub = equalise (hint_ctx hint) ctx

      equalise ctx1 ctx2 =
        zip (exprs (fmap fst m)) (exprs (fmap snd m))
        where
          m = Map.intersectionWith (,) ctx1 ctx2

-- A typeclass for values that contain SMT expressions.
class Exprs a where
  -- List SMT expressions contained inside a value.
  exprs :: a -> [SExpr]

instance Exprs Entry where
  exprs (Entry x) = exprs x

instance Exprs Context where
  exprs = concatMap exprs . Map.elems

----------------------------------------------------------------------
-- The context.
----------------------------------------------------------------------

type Context = Map Name Entry
data Name  = forall a. (Typeable a, Ord a, Mergeable a, Show a, ShowModel a, Invariant a, Exprs a) => Name String a
data Entry = forall a. (Typeable a, Ord a, Mergeable a, Show a, ShowModel a, Invariant a, Exprs a) => Entry a

instance Eq Name where x == y = compare x y == EQ
instance Ord Name where
  compare = comparing (\(Name name x) -> (name, typeOf x))
instance Show Name where show (Name name _) = name

instance Eq Entry where
  Entry x == Entry y = typeOf x == typeOf y && cast x == Just y
instance Ord Entry where
  compare (Entry x) (Entry y) =
    compare (typeOf x) (typeOf y) `mappend`
    compare (Just x) (cast y)
instance Show Entry where
  showsPrec n (Entry x) = showsPrec n x

-- Look up a value in the context.
lookupContext :: forall a. (Typeable a, Ord a, Mergeable a, Show a, ShowModel a, Invariant a, Exprs a) => String -> Context -> a
lookupContext name ctx =
  case Map.lookup (Name name (undefined :: a)) ctx of
    Nothing -> error ("variable " ++ name ++ " not found in context")
    Just (Entry x) ->
      case cast x of
        Nothing -> error "type mismatch in lookup"
        Just x  -> x

-- Add a value to the context or modify an existing binding.
insertContext :: forall a. (Typeable a, Ord a, Mergeable a, Show a, ShowModel a, Invariant a, Exprs a) => String -> a -> Context -> Context
insertContext name x ctx = Map.insert (Name name (undefined :: a)) (Entry x) ctx

-- modified ctx1 ctx2 returns a subset of ctx2 that contains
-- only the values that have been changed from ctx1.
modified :: Context -> Context -> Context
modified ctx1 ctx2 =
  Map.mergeWithKey f (const Map.empty) (const Map.empty) ctx1 ctx2
  where
    f _ x y
      | x == y    = Nothing
      | otherwise = Just y

-- A typeclass for values that support if-then-else.
class Mergeable a where
  merge :: SExpr -> a -> a -> a

mergeContext :: SExpr -> Context -> Context -> Verify Context
mergeContext cond ctx1 ctx2 =
  -- If a variable is bound conditionally, put it in the result
  -- context, but only define it conditionally.
  sequence $
    Map.mergeWithKey
      (const combine)
      (fmap (definedWhen cond))
      (fmap (definedWhen (SMT.not cond)))
      ctx1 ctx2
  where
    combine :: Entry -> Entry -> Maybe (Verify Entry)
    combine x y = Just (return (merge cond x y))

    definedWhen :: SExpr -> Entry -> Verify Entry
    definedWhen cond (Entry x) = do
      y <- fresh "unbound"
      return (Entry (merge cond x y))

instance Mergeable Entry where
  merge cond (Entry x) (Entry y) =
    case cast y of
      Just y  -> Entry (merge cond x y)
      Nothing -> error "incompatible types in merge"

instance Mergeable SExpr where
  merge cond t e
    | t == e = t
    | cond == bool True  = t
    | cond == bool False = e
    | otherwise = SMT.ite cond t e

-- A typeclass for values that can be shown given a model from
-- the SMT solver.
class ShowModel a where
  showModel :: a -> Verify String

instance ShowModel Context where
  showModel ctx = do
    let (keys, values) = unzip (Map.toList ctx)
    values' <- mapM showModel values
    return (intercalate ", " (zipWith (\(Name k _) v -> k ++ " = " ++ v) keys values'))

instance ShowModel Entry where
  showModel (Entry x) = showModel x

instance ShowModel SExpr where
  showModel x = do
    val <- lift (getExpr x)
    return (showValue val)

----------------------------------------------------------------------
-- The different bindings that are stored in the context.
----------------------------------------------------------------------

-- A normal variable binding.
data ValBinding exp a =
  ValBinding {
    vb_value :: SMTExpr exp a,
    vb_ref   :: Maybe String }
  deriving (Eq, Ord, Show, Typeable)
instance SMTEval exp a => Mergeable (ValBinding exp a) where
  merge cond x y =
    case (vb_ref x, vb_ref y) of
      (Just r1, Just r2) | r1 /= r2 ->
        error "immutable binding bound in two locations"
      _ ->
        ValBinding {
          vb_value = merge cond (vb_value x) (vb_value y),
          vb_ref   = vb_ref x `mplus` vb_ref y }
instance SMTEval exp a => ShowModel (ValBinding exp a) where
  showModel = showModel . vb_value
instance SMTEval exp a => Fresh (ValBinding exp a) where
  fresh name = do
    val <- fresh name
    return (ValBinding val Nothing)
instance SMTEval exp a => Invariant (ValBinding exp a) where
  data Literal (ValBinding exp a) = LitVB
    deriving (Eq, Ord, Show, Typeable)
  havoc name = error ("immutable binding " ++ name ++ " rebound")
instance SMTEval exp a => IsLiteral (Literal (ValBinding exp a))
instance SMTEval exp a => Exprs (ValBinding exp a) where
  exprs val = [toSMT (vb_value val)]

peekVal :: forall exp a. SMTEval exp a => String -> Verify (SMTExpr exp a)
peekVal name = do
  ValBinding val ref <- peek name
  case ref of
    Nothing -> return ()
    Just refName -> do
      ref <- peek refName :: Verify (RefBinding exp a)
      safe <- provable "reference not frozen" (val .==. rb_value ref)
      unless safe (warn ("Unsafe use of frozen reference " ++ name))
  return val

pokeVal :: SMTEval exp a => String -> SMTExpr exp a -> Verify ()
pokeVal name val = poke name (ValBinding val Nothing)

-- A binding for a reference.
data RefBinding exp a =
  RefBinding {
    rb_value       :: SMTExpr exp a,
    rb_initialised :: SExpr }
  deriving (Eq, Ord, Show, Typeable)

instance SMTEval exp a => Mergeable (RefBinding exp a) where
  merge cond (RefBinding v1 i1) (RefBinding v2 i2) =
    RefBinding (merge cond v1 v2) (merge cond i1 i2)
instance SMTEval exp a => ShowModel (RefBinding exp a) where
  showModel = showModel . rb_value
instance SMTEval exp a => Fresh (RefBinding exp a) where
  fresh name = do
    value   <- fresh name
    init    <- freshVar (name ++ ".init") tBool
    return (RefBinding value init)
instance SMTEval exp a => Invariant (RefBinding exp a) where
  data Literal (RefBinding exp a) =
      RefInitialised String
    | RefUnchanged String
    deriving (Eq, Ord, Show, Typeable)

  literals name _ = [RefInitialised name, RefUnchanged name]
instance SMTEval exp a => IsLiteral (Literal (RefBinding exp a)) where
  smtLit _ ctx (RefInitialised name) =
    rb_initialised (lookupContext name ctx :: RefBinding exp a)
  smtLit old new (RefUnchanged name) =
    toSMT (rb_value x) `eq` toSMT (rb_value y)
    where
      x, y :: RefBinding exp a
      x = lookupContext name old
      y = lookupContext name new
instance SMTEval exp a => Exprs (RefBinding exp a) where
  exprs ref = [toSMT (rb_value ref), rb_initialised ref]

newRef :: SMTEval exp a => String -> exp a -> Verify ()
newRef name (_ :: exp a) = do
  ref <- fresh name
  poke name (ref { rb_initialised = bool False } :: RefBinding exp a)

getRef :: SMTEval exp a => String -> Verify (SMTExpr exp a)
getRef name = do
  ref <- peek name
  safe <- provable "reference initialised" (rb_initialised ref)
  unless safe (warn (name ++ " read before initialisation"))
  return (rb_value ref)

setRef :: forall exp a. SMTEval exp a => String -> SMTExpr exp a -> Verify ()
setRef name val = do
  ref <- peek name :: Verify (RefBinding exp a)
  poke name ref{rb_value = val, rb_initialised = bool True}

unsafeFreezeRef :: forall exp a. SMTEval exp a => String -> String -> exp a -> Verify ()
unsafeFreezeRef refName valName (_ :: exp a) = do
  ref <- peek refName :: Verify (RefBinding exp a)
  poke valName (ValBinding (rb_value ref) (Just refName))

-- An array binding.
data ArrBinding exp i a =
  ArrBinding {
    arr_value  :: SMTArray exp i a,
    arr_bound  :: SMTExpr exp i }
  deriving (Eq, Ord, Typeable, Show)
instance (SMTEval exp a, SMTEval exp i) => Mergeable (ArrBinding exp i a) where
  merge cond (ArrBinding v1 b1) (ArrBinding v2 b2) =
    ArrBinding (merge cond v1 v2) (merge cond b1 b2)
instance (SMTEval exp a, SMTEval exp i) => ShowModel (ArrBinding exp i a) where
  showModel arr = lift $ do
    bound <- getExpr (toSMT (arr_bound arr))
    showArray bound (toSMT (arr_value arr))
instance (SMTEval exp a, SMTEval exp i) => Fresh (ArrBinding exp i a) where
  fresh name = do
    arr   <- fresh name
    bound <- fresh (name ++ ".bound")
    return (ArrBinding arr bound)
instance (SMTEval exp a, SMTEval exp i) => Invariant (ArrBinding exp i a) where
  data Literal (ArrBinding exp i a) = LitAB
    deriving Typeable
instance (SMTEval exp a, SMTEval exp i) => IsLiteral (Literal (ArrBinding exp i a))
deriving instance SMTEval exp a => Eq   (Literal (ArrBinding exp i a))
deriving instance SMTEval exp a => Ord  (Literal (ArrBinding exp i a))
deriving instance SMTEval exp a => Show (Literal (ArrBinding exp i a))
instance (SMTEval exp a, SMTEval exp i) => Exprs (ArrBinding exp i a) where
  exprs arr = [toSMT (arr_value arr), toSMT (arr_bound arr)]

data IArrBinding exp i a =
  IArrBinding {
    iarr_value  :: SMTArray exp i a,
    iarr_bound  :: SMTExpr exp i,
    iarr_origin :: Maybe String }
  deriving (Eq, Ord, Typeable, Show)
instance (SMTEval exp a, SMTEval exp i) => Mergeable (IArrBinding exp i a) where
  merge cond x y =
    case (iarr_origin x, iarr_origin y) of
      (Just a1, Just a2) | a1 /= a2 ->
        error "immutable array bound in two locations"
      _ ->
        IArrBinding {
          iarr_value  = merge cond (iarr_value x) (iarr_value y),
          iarr_bound  = merge cond (iarr_bound x) (iarr_bound y),
          iarr_origin = iarr_origin x `mplus` iarr_origin y }
instance (SMTEval exp a, SMTEval exp i) => ShowModel (IArrBinding exp i a) where
  showModel arr = lift $ do
    bound <- getExpr (toSMT (iarr_bound arr))
    showArray bound (toSMT (iarr_value arr))
instance (SMTEval exp a, SMTEval exp i) => Fresh (IArrBinding exp i a) where
  fresh name = do
    arr   <- fresh name
    bound <- fresh (name ++ ".bound")
    return (IArrBinding arr bound Nothing)
instance (SMTEval exp a, SMTEval exp i) => Invariant (IArrBinding exp i a) where
  data Literal (IArrBinding exp i a) = LitIAB
    deriving Typeable
  havoc name = error ("immutable array " ++ name ++ " rebound")
instance (SMTEval exp a, SMTEval exp i) => IsLiteral (Literal (IArrBinding exp i a))
deriving instance SMTEval exp a => Eq   (Literal (IArrBinding exp i a))
deriving instance SMTEval exp a => Ord  (Literal (IArrBinding exp i a))
deriving instance SMTEval exp a => Show (Literal (IArrBinding exp i a))
instance (SMTEval exp a, SMTEval exp i) => Exprs (IArrBinding exp i a) where
  exprs arr = [toSMT (iarr_value arr), toSMT (iarr_bound arr)]

-- A wrapper to help with fresh name generation.
newtype SMTArray exp i a = SMTArray SExpr deriving (Eq, Ord, Show, Mergeable)
instance (SMTEval exp a, SMTEval exp i) => Fresh (SMTArray exp i a) where
  fresh = freshSExpr
instance (SMTEval exp a, SMTEval exp i) => TypedSExpr (SMTArray exp i a) where
  smtType _ = tArray (smtType (undefined :: SMTExpr exp i)) (smtType (undefined :: SMTExpr exp a))
  toSMT (SMTArray arr) = arr
  fromSMT = SMTArray

arrIx :: forall exp i a. (SMTEval exp i, SMTEval exp a) => String -> SMTExpr exp i -> Verify (SMTExpr exp a)
arrIx name ix = do
  iarr <- peek name :: Verify (IArrBinding exp i a)
  case iarr_origin iarr of
    Nothing -> return ()
    Just arrName -> do
      arr <- peek arrName :: Verify (ArrBinding exp i a)
      safe <- provable "array not modified" (iarr_value iarr .==. arr_value arr)
      unless safe (warn ("Unsafe use of frozen array " ++ name))
  return (fromSMT (select (toSMT (iarr_value iarr)) (toSMT ix)))

----------------------------------------------------------------------
-- Instances for the standard non-control flow command datatypes.
----------------------------------------------------------------------

-- A couple of utility functions for getting at witnesses.
withWitness :: forall instr prog exp pred a b.
  (SMTEval1 exp, Pred exp a) =>
  a -> instr '(prog, Param2 exp pred) b ->
  (SMTEval exp a => Verify ()) ->
  Verify (instr '(prog, Param2 exp pred) b)
withWitness (x :: a) instr m
  | Dict <- witnessPred (undefined :: exp a) = do
    m
    return instr

producesValue :: forall instr prog exp a.
  (SMTEval1 exp, Pred exp a) =>
  instr '(prog, Param2 exp (Pred exp)) (Val a) -> Val a ->
  Verify (instr '(prog, Param2 exp (Pred exp)) (Val a))
producesValue instr (ValComp name :: Val a) =
  withWitness (undefined :: a) instr $ do
    val <- fresh name
    pokeVal name (val :: SMTExpr exp a)

instance (pred ~ Pred exp, SMTEval1 exp) => VerifyInstr FileCMD exp pred where
  verifyInstr instr@FGet{} val = producesValue instr val
  verifyInstr instr@(FPrintf _ _ as) _ = do
    let
      evalArg :: PrintfArg exp pred -> Verify ()
      evalArg (PrintfArg (exp :: exp a)) =
        case witnessPred (undefined :: exp a) of
          Dict -> void (eval exp)
    mapM_ evalArg as
    return instr
  verifyInstr instr _ = return instr

instance (pred ~ Pred exp, SMTEval1 exp) => VerifyInstr C_CMD exp pred where
  verifyInstr = error "Don't know how to verify C_CMD"

instance (pred ~ Pred exp, SMTEval1 exp) => VerifyInstr RefCMD exp pred where
  verifyInstr instr@NewRef{} ref@(RefComp name :: Ref a) =
    withWitness (undefined :: a) instr $ do
      newRef name (undefined :: exp a)

  verifyInstr instr@(InitRef _ expr) (RefComp name :: Ref a) =
    withWitness (undefined :: a) instr $ do
      newRef name (undefined :: exp a)
      eval expr >>= setRef name

  verifyInstr instr@(GetRef (RefComp refName)) (ValComp valName :: Val a) =
    withWitness (undefined :: a) instr $ do
      val <- getRef refName :: Verify (SMTExpr exp a)
      pokeVal valName val

  verifyInstr instr@(SetRef (RefComp name :: Ref a) expr) () =
    withWitness (undefined :: a) instr $ do
      eval expr >>= setRef name

  verifyInstr instr@(UnsafeFreezeRef (RefComp refName)) (ValComp valName :: Val a) =
    withWitness (undefined :: a) instr $ do
      unsafeFreezeRef refName valName (undefined :: exp a)

instance (Pred exp ~ pred, SMTEval1 exp) => VerifyInstr ArrCMD exp pred where
  verifyInstr instr@(NewArr _ n) arr@(ArrComp name :: Arr i a)
    | Dict <- witnessPred (undefined :: exp i) =
    withWitness (undefined :: a) instr $ do
      val <- fresh name
      n   <- eval n
      poke name (ArrBinding val n :: ArrBinding exp i a)

  verifyInstr instr@(InitArr _ xs) arr@(ArrComp name :: Arr i a)
    | Dict <- witnessPred (undefined :: exp i),
      Dict <- witnessNum (undefined :: exp i) =
    withWitness (undefined :: a) instr $ do
      val <- fresh name
      let
        is :: [SMTExpr exp i]
        is = map fromConstant [0..]

        ys :: [SMTExpr exp a]
        ys = map fromConstant xs

        n = fromIntegral (length xs)

      forM_ (zip is ys) $ \(i, x) ->
        assume "array initialisation" (select (toSMT val) (toSMT i) `eq` toSMT x)

      poke name (ArrBinding val n :: ArrBinding exp i a)

  verifyInstr instr@(GetArr ix (ArrComp arrName :: Arr i a)) (ValComp valName)
    | Dict <- witnessPred (undefined :: exp i) =
    withWitness (undefined :: a) instr $ do
      arr <- peek arrName :: Verify (ArrBinding exp i a)
      ix  <- eval ix
      let val = fromSMT (select (toSMT (arr_value arr)) (toSMT ix))
      pokeVal valName (val :: SMTExpr exp a)

  verifyInstr instr@(SetArr ix val (ArrComp arrName :: Arr i a)) ()
    | Dict <- witnessPred (undefined :: exp i) =
    withWitness (undefined :: a) instr $ do
      ArrBinding{..} <- peek arrName :: Verify (ArrBinding exp i a)
      ix  <- eval ix
      val <- eval val
      let arr_value' = fromSMT (store (toSMT arr_value) (toSMT ix) (toSMT val))
      poke arrName (ArrBinding arr_value' arr_bound :: ArrBinding exp i a)

  verifyInstr instr@(CopyArr (ArrComp destName :: Arr i a, destOfs) (ArrComp srcName, srcOfs) len) ()
    | Dict <- witnessPred (undefined :: exp i) =
    withWitness (undefined :: a) instr $ do
      dest <- peek destName :: Verify (ArrBinding exp i a)
      src  <- peek destName :: Verify (ArrBinding exp i a)
      destOfs <- eval destOfs
      srcOfs  <- eval srcOfs
      len     <- eval len

      -- XXX for now, leave the destination uninterpreted
      -- (should introduce a new fun and transform it to an array)
      dest' <- fresh "copy"
      poke destName (ArrBinding dest' (arr_bound dest) :: ArrBinding exp i a)

  verifyInstr instr@(UnsafeFreezeArr (ArrComp arrName :: Arr i a)) (IArrComp iarrName)
    | Dict <- witnessPred (undefined :: exp i) =
    withWitness (undefined :: a) instr $ do
      arr <- peek arrName :: Verify (ArrBinding exp i a)
      poke iarrName (IArrBinding (arr_value arr) (arr_bound arr) (Just arrName))

  verifyInstr instr@(UnsafeThawArr (IArrComp iarrName :: IArr i a)) (ArrComp arrName) =
    error "don't know how to thaw arrays, sorry"

instance VerifyInstr ThreadCMD exp pred where
  verifyInstr = error "can't verify ThreadCMD"
instance VerifyInstr ChanCMD exp pred where
  verifyInstr = error "can't verify ChanCMD"
instance VerifyInstr PtrCMD exp pred where
  verifyInstr = error "can't verify PtrCMD"

----------------------------------------------------------------------
-- An instance for ControlCMD - where the magic happens
----------------------------------------------------------------------

instance (Pred exp ~ pred, SMTEval1 exp, Pred exp Bool, SMTEval exp Bool) => VerifyInstr ControlCMD exp pred where
  verifyInstr (Assert Nothing msg) () =
    return (Assert Nothing msg)
  verifyInstr (Assert (Just cond) msg) () = do
    b <- eval cond
    res <- provable "assertion" (toSMT b)
    if res then
      return (Assert Nothing msg)
    else do
      assume "assertion" (toSMT b)
      return (Assert (Just cond) msg)
  verifyInstr instr@(CMD.Hint (exp :: exp a)) () =
    withWitness (undefined :: a) instr $ do
      x <- eval exp
      hint x
  verifyInstr Break () = do
    break
    return Break
  verifyInstr (If cond t e) () = do
    b <- eval cond
    (t', e') <- ite (toSMT b) (verify t) (verify e)
    hintFormula (toSMT b)
    hintFormula (SMT.not (toSMT b))
    return (If cond t' e')
  verifyInstr (While cond body) () = do
    let
      loop = do
        res <- verifyWithResult cond >>= eval . snd
        ite (toSMT res) (verify body) break
        return ()
    finished <- discoverInvariant loop
    (cond', body') <- stack $ do
      (cond', res) <- verifyWithResult cond
      eval res >>= assume "loop guard" . toSMT
      body' <- verify body
      return (cond', body')
    finished
    return (While cond' body')
  verifyInstr (For range@(lo, step, hi) val@(ValComp name :: Val a) body) ()
    | Dict <- witnessPred (undefined :: exp a),
      Dict <- witnessNum (undefined :: exp a),
      Dict <- witnessOrd (undefined :: exp a) = do
      let
        cond = do
          unsafeFreezeRef name name (undefined :: exp a)
          i <- peekVal name
          n <- eval (borderVal hi)
          m <- eval lo
          hintFormula (m .<=. i)
          hintFormula (i .<=. n)
          return (if borderIncl hi then i .<=. n else i .<. n)
        loop = do
          cond <- cond
          ite (SMT.not cond) break $ do
            breaks <- breaks (verify body)
            ite breaks (return ()) $ do
              i <- peekVal name :: Verify (SMTExpr exp a)
              setRef name (i + fromIntegral step)
          return ()
      m <- eval lo
      newRef name (undefined :: exp a)
      setRef name m
      finished <- discoverInvariant loop
      body' <- stack (cond >>= assume "loop guard" >> verify body)
      finished
      return (For range val body')

-- The literals used in predicate abstraction.
data SomeLiteral = forall a. IsLiteral a => SomeLiteral a

instance Eq SomeLiteral where x == y = compare x y == EQ
instance Ord SomeLiteral where
  compare (SomeLiteral x) (SomeLiteral y) =
    compare (typeOf x) (typeOf y) `mappend`
    case cast y of
      Just y  -> compare x y
      Nothing -> error "weird type error"

instance Show SomeLiteral where show (SomeLiteral x) = show x

-- Takes a loop body, which should break on exit, and does predicate abstraction.
-- Leaves the verifier in a state which represents an arbitrary loop iteration.
-- Returns a value which when run leaves the verifier in a state where the loop
-- has terminated.
discoverInvariant :: Verify () -> Verify (Verify ())
discoverInvariant body = do
  (frame, hints) <- findFrameAndHints
  (_, _, mode) <- ask
  case mode of
    Prove -> do
      ctx <- get
      abstract ctx frame hints >>= refine frame hints
    Execute -> do
      assumeLiterals frame []
      return (noBreak (breaks body) >>= assume "loop terminated")
  where
    -- Suppose we have a while-loop while(E) S, and we know a formula
    -- I(0) which describes the initial state of the loop.
    --
    -- We can describe the state after one iteration by the formula
    --   I(1) := sp(S, I(0) /\ ~E)
    -- where sp(S, P) is the strongest postcondition function.
    -- Likewise, we can describe the state after n+1 iterations by:
    --   I(n+1) := sp(S, I(n) /\ ~E)
    -- The invariant of the loop is then simply
    --   I := I(0) \/ I(1) \/ I(2) \/ ...
    --
    -- Of course, this invariant is infinite and not very useful.
    --
    -- The idea of predicate abstraction is this: if we restrict the
    -- invariant to be a boolean formula built up from a fixed set of
    -- literals, then there are only a finite number of possible
    -- invariants and we can in fact compute an invariant using the
    -- procedure above - at some point I(n+1) = I(n) and then I(n) is
    -- the invariant. We just need to be able to compute the strongest
    -- boolean formula provable in the current verifier state -
    -- something which Abstract.hs provides.
    --
    -- Often a variable is not modified by the loop body, and in that
    -- case we don't need to bother finding an invariant for that
    -- variable - its value is the same as on entry to the loop. We
    -- therefore also compute the set of variables modified by the
    -- loop body, which we call the frame, and only consider literals
    -- that mention frame variables. We do not need to do anything
    -- explicitly for non-frame variables - it is enough to leave them
    -- unchanged in the context when verifying the loop body.
    --
    -- Recall that the goal is to put the verifier in a state
    -- representing an arbitrary loop iteration. Here is how we do
    -- that:
    --   * Find n such that I(n) = I(n+1).
    --   * Havoc the frame variables (update the context to turn them
    --     into fresh SMT variables). This puts the SMT solver in a
    --     state where it knows nothing about those variables, but it
    --     still knows the values of the non-frame variables.
    --   * Assert that I(n) holds.
    --
    -- To find the invariant we must be able to compute I(0),
    -- and to go from I(n) to I(n+1). To compute I(0), we just run
    -- predicate abstraction in the state we initially find ourselves
    -- in. To get from I(n) to I(n+1) we do the following:
    --   * Havoc the frame variables and then assert I(n). Similar to
    --     above, this tells the verifier that we are in an arbitrary
    --     state in which I(n) holds.
    --   * Assert that the loop has not terminated yet, execute the
    --     loop body once, and use predicate abstraction to compute a
    --     new formula P describing the state we are in now.
    --     This corresponds to sp(S, I(n) /\ ~E). Then let
    --     I(n+1) = I(n) \/ P.
    -- Note that we do all this inside a call to "stack" so that
    -- it doesn't permanently change the verifier state.

    findFrameAndHints = stack $ quietly $ noWarn $ quickly $ do
      -- Put the verifier in an arbitrary state.
      ctx <- get
      let
        op ctx (Name name (_ :: a)) = do
          val <- fresh name
          return (insertContext name (val :: a) ctx)
      before <- foldM op Map.empty (Map.keys ctx)
      put before

      -- Run the program and see what changed.
      (_, _, hints, decls) <- fmap snd (listen body)
      after <- get

      let
        atoms (Atom x) = [x]
        atoms (List xs) = concatMap atoms xs

        hints' =
          [ Hint before hint
          | hint <- nub hints,
            null (intersect decls (atoms (hb_exp hint))) ]

      return (Map.keys (modified before after), hints')

    refine frame hints clauses = do
      ctx <- get
      clauses' <- stack $ quietly $ noWarn $ do
        assumeLiterals frame clauses
        noBreak (breaks body) >>= assume "loop not terminated" . SMT.not
        fmap (disjunction clauses) (chattily (abstract ctx frame hints))

      if clauses == clauses' then do
        assumeLiterals frame clauses
        return (noBreak (breaks body) >>= assume "loop terminated")
      else refine frame hints clauses'

    assumeLiterals :: [Name] -> [[SomeLiteral]] -> Verify ()
    assumeLiterals frame clauses = do
      ctx <- get
      forM_ frame $ \(Name name (_ :: a)) -> do
        val <- peek name >>= havoc name
        poke name (val :: a)
      mapM_ (evalClause ctx >=> assume "invariant") clauses

    evalClause old clause = do
      ctx <- get
      return (disj [ smtLit old ctx lit | SomeLiteral lit <- clause ])

    abstract old frame hints = fmap (usort . map usort) $ do
      ctx <- get
      res <- quietly $ Abstract.abstract (evalClause old >=> provable "invariant") (lits frame)
      chat $ liftIO $
        case res of
          [] -> putStrLn ("No invariant found over frame " ++ show frame)
          [clause] -> putStrLn ("Possible invariant " ++ show clause ++ " over frame " ++ show frame)
          _ -> do
            putStrLn ("Possible invariant over frame " ++ show frame ++ ":")
            sequence_ [ putStrLn ("  " ++ show clause) | clause <- res ]
      return res
      where
        lits frame =
          concat [ map SomeLiteral (literals name x) | Name name x <- frame ] ++
          [ SomeLiteral hint | hint <- hints, hb_type (hint_body hint) == tBool ]

    disjunction cs1 cs2 =
      prune (usort [ usort (c1 ++ c2) | c1 <- cs1, c2 <- cs2 ])
      where
        prune cs = [ c | c <- cs, and [ c == c' || c' \\ c /= [] | c' <- cs ] ]

    usort :: Ord a => [a] -> [a]
    usort = map head . group . sort
