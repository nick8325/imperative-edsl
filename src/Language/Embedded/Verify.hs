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
import Language.Embedded.Verify.FirstOrder
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
--        "chattiness level" (if > 0 then tracing messages are printed)
-- Write: disjunction which is true if the program has called break;
--        list of warnings generated
-- State: the context, a map from variables to SMT values
type Verify = RWST ([SExpr], Int) ([SExpr], [String]) Context SMT

runVerify :: Verify a -> IO (a, [String])
runVerify m = runZ3 ["-t:1000"] $ do
  SMT.setOption ":produce-models" "false"
  (x, (_, warns)) <- evalRWST m ([], 0) Map.empty
  return (x, warns)

-- Assume that a given formula is true.
assume :: SExpr -> Verify ()
assume p = do
  branch <- branch
  trace "Asserted" p
  lift (assert (disj (p:map SMT.not branch)))

-- Check if a given formula holds.
provable :: SExpr -> Verify Bool
provable p = do
  branch <- branch
  stack $ do
    res <- lift $ do
      mapM_ assert branch
      assert (SMT.not p)
      check
    chat $
      case res of
        Sat -> stack $ do
          trace "Failed to prove" p
          lift $ setOption ":produce-models" "true"
          lift $ check
          context <- get
          model   <- showModel context
          liftIO $ putStrLn ("  (countermodel is " ++ model ++ ")")
        Unsat   -> trace "Proved" p
        Unknown -> trace "Couldn't solve" p
    return (res == Unsat)

-- Print a formula for debugging purposes.
trace :: String -> SExpr -> Verify ()
trace kind p = chat $ do
  branch <- branch

  liftIO $ do
    putStr (kind ++ " " ++ show p)
    case branch of
      [] -> putStrLn ""
      [x] -> do
        putStrLn (" assuming " ++ show x)
      _ -> do
        putStrLn " assuming:"
        sequence_ [ putStrLn ("  " ++ show x) | x <- branch ]

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
      | p == bool False = local (\(_,  x) -> ([p],  x))
      | otherwise       = local (\(xs, x) -> (p:xs, x))
  (x, ctx1, (break1, warns1)) <- lift $ runRWST (withBranch p mx) read ctx
  (y, ctx2, (break2, warns2)) <- lift $ runRWST (withBranch (SMT.not p) my) read ctx
  put (merge p ctx1 ctx2)
  let
    break
      | null break1 && null break2 = []
      | otherwise = [SMT.ite p (disj break1) (disj break2)]
  tell (break, warns1 ++ warns2)
  return (x, y)

-- Read the current branch.
branch :: Verify [SExpr]
branch = asks fst

-- Read the context.
peek :: (Typeable a, Eq a, Mergeable a, Show a, ShowModel a, Invariant a) => String -> Verify a
peek name = do
  ctx <- get
  return (lookupContext name ctx)

-- Write to the context.
poke :: (Typeable a, Eq a, Mergeable a, Show a, ShowModel a, Invariant a) => String -> a -> Verify ()
poke name val = modify (insertContext name val)

-- Record that execution has broken here.
break :: Verify ()
break = do
  branch <- branch
  tell ([conj branch], [])

-- Check if execution of a statement can break.
withBreaks :: Verify a -> Verify (a, SExpr)
withBreaks mx = do
  (x, (exits, _)) <- listen mx
  return (x, disj exits)

-- Check if execution of a statement can break, discarding the
-- statement's result.
breaks :: Verify a -> Verify SExpr
breaks mx = fmap snd (withBreaks mx)

-- Prevent a statement from breaking.
noBreak :: Verify a -> Verify a
noBreak = censor (\(_, warns) -> ([], warns))

-- Add a warning to the output.
warn :: String -> Verify ()
warn msg = tell ([], [msg])

-- Run a computation but ignoring its warnings.
noWarn :: Verify a -> Verify a
noWarn = censor (\(breaks, _) -> (breaks, []))

-- Run a computation more chattily.
chattily :: Verify a -> Verify a
chattily = local (\(ctx, n) -> (ctx, n+1))

-- Run a computation more quietly.
quietly :: Verify a -> Verify a
quietly = local (\(ctx, n) -> (ctx, n-1))

-- Produce debug output.
chat :: Verify () -> Verify ()
chat mx = do
  (_, chatty) <- ask
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
  
  witnessIntegral :: Integral a => exp a -> Dict (Num (SMTExpr exp a))
  witnessIntegral = error "witnessIntegral"

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

instance SMTEval exp a => Show (SMTExpr exp a) where
  showsPrec n x = showsPrec n (toSMT x)

instance SMTEval exp a => Mergeable (SMTExpr exp a) where
  merge cond x y = fromSMT (merge cond (toSMT x) (toSMT y))

instance SMTEval exp a => ShowModel (SMTExpr exp a) where
  showModel x = showModel (toSMT x)

instance SMTEval exp a => Fresh (SMTExpr exp a) where
  fresh name =
    fmap fromSMT (freshVar name (smtType (undefined :: SMTExpr exp a)))

-- Bind an expression into an SMT variable to increase sharing.
share :: TypedSExpr a => a -> Verify a
share exp = do
  x <- fresh "let"
  assume (x .==. exp)
  return x

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
  lift $ declare (name ++ show n) ty

-- A typeclass for values that can undergo predicate abstraction.
class (Ord (Literal a), Typeable (Literal a), Show (Literal a), Fresh a) => Invariant a where
  data Literal a

  -- Forget the value of a binding.
  havoc :: String -> a -> Verify a
  havoc name _ = fresh name

  -- Return a list of candidate literals for a value.
  literals :: String -> a -> [Literal a]
  literals _ _ = []

  -- Evaluate a literal.
  smtLit :: Context -> String -> Literal a -> SExpr
  smtLit _ _ _ = error "smtLit not defined"

----------------------------------------------------------------------
-- The context.
----------------------------------------------------------------------

type Context = Map Name Entry
data Name  = forall a. (Typeable a, Eq a, Mergeable a, Show a, ShowModel a, Invariant a) => Name String a
data Entry = forall a. (Typeable a, Eq a, Mergeable a, Show a, ShowModel a, Invariant a) => Entry a

instance Eq Name where x == y = compare x y == EQ
instance Ord Name where
  compare = comparing (\(Name name x) -> (name, typeOf x))
instance Show Name where show (Name name _) = name

instance Eq Entry where
  Entry x == Entry y = typeOf x == typeOf y && cast x == Just y
instance Show Entry where
  showsPrec n (Entry x) = showsPrec n x

-- Look up a value in the context.
lookupContext :: forall a. (Typeable a, Eq a, Mergeable a, Show a, ShowModel a, Invariant a) => String -> Context -> a
lookupContext name ctx =
  case Map.lookup (Name name (undefined :: a)) ctx of
    Nothing -> error ("variable " ++ name ++ " not found in context")
    Just (Entry x) ->
      case cast x of
        Nothing -> error "type mismatch in lookup"
        Just x  -> x

-- Add a value to the context or modify an existing binding.
insertContext :: forall a. (Typeable a, Eq a, Mergeable a, Show a, ShowModel a, Invariant a) => String -> a -> Context -> Context
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

instance Mergeable Context where
  merge cond = Map.intersectionWith (merge cond)

instance Mergeable Entry where
  merge cond (Entry x) (Entry y) =
    case cast y of
      Just y  -> Entry (merge cond x y)
      Nothing -> error "incompatible types in merge"

instance Mergeable SExpr where
  merge cond t e
    | t == e = t
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
    return (show val)

----------------------------------------------------------------------
-- The different bindings that are stored in the context.
----------------------------------------------------------------------

-- A normal variable binding.
data ValBinding exp a =
  ValBinding {
    vb_value :: SMTExpr exp a,
    vb_ref   :: Maybe String }
  deriving (Eq, Show, Typeable)
instance SMTEval exp a => Mergeable (ValBinding exp a) where
  merge _ x y
    | x == y = x
    | otherwise = error "immutable binding bound in two locations"
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

peekVal :: forall exp a. SMTEval exp a => String -> Verify (SMTExpr exp a)
peekVal name = do
  ValBinding val ref <- peek name
  case ref of
    Nothing -> return ()
    Just refName -> do
      ref <- peek refName :: Verify (RefBinding exp a)
      safe <- provable (val .==. rb_value ref)
      unless safe (warn ("Unsafe use of frozen reference " ++ name))
  return val

pokeVal :: SMTEval exp a => String -> SMTExpr exp a -> Verify ()
pokeVal name val = poke name (ValBinding val Nothing)

-- A binding for a reference.
data RefBinding exp a =
  RefBinding {
    rb_value       :: SMTExpr exp a,
    rb_initialised :: SExpr }
  deriving (Eq, Show, Typeable)

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
  data Literal (RefBinding exp a) = RefInitialised | RefWritable
    deriving (Eq, Ord, Show, Typeable)

  literals _ _ = [RefInitialised]

  smtLit ctx name RefInitialised =
    rb_initialised (lookupContext name ctx :: RefBinding exp a)

newRef :: SMTEval exp a => String -> exp a -> Verify ()
newRef name (_ :: exp a) = do
  ref <- fresh name
  poke name (ref { rb_initialised = bool False } :: RefBinding exp a)

getRef :: SMTEval exp a => String -> Verify (SMTExpr exp a)
getRef name = do
  ref <- peek name
  safe <- provable (rb_initialised ref)
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
    arr_value :: SMTArray exp i a,
    arr_bound :: SMTExpr exp i }
  deriving (Eq, Typeable, Show)
instance (SMTEval exp a, SMTEval exp i) => Mergeable (ArrBinding exp i a) where
  merge cond (ArrBinding v1 b1) (ArrBinding v2 b2) =
    ArrBinding (merge cond v1 v2) (merge cond b1 b2)
instance (SMTEval exp a, SMTEval exp i) => ShowModel (ArrBinding exp i a) where
  showModel _ = return "<array>"
instance (SMTEval exp a, SMTEval exp i) => Fresh (ArrBinding exp i a) where
  fresh name = do
    arr   <- fresh name
    bound <- fresh (name ++ ".bound")
    return (ArrBinding arr bound)
instance (SMTEval exp a, SMTEval exp i) => Invariant (ArrBinding exp i a) where
  data Literal (ArrBinding exp i a) = LitAB
    deriving Typeable
deriving instance SMTEval exp a => Eq   (Literal (ArrBinding exp i a))
deriving instance SMTEval exp a => Ord  (Literal (ArrBinding exp i a))
deriving instance SMTEval exp a => Show (Literal (ArrBinding exp i a))

-- A wrapper to help with fresh name generation.
newtype SMTArray exp i a = SMTArray SExpr deriving (Eq, Ord, Show, Mergeable)
instance (SMTEval exp a, SMTEval exp i) => Fresh (SMTArray exp i a) where
  fresh = freshSExpr
instance (SMTEval exp a, SMTEval exp i) => TypedSExpr (SMTArray exp i a) where
  smtType _ = tArray (smtType (undefined :: SMTExpr exp i)) (smtType (undefined :: SMTExpr exp a))
  toSMT (SMTArray arr) = arr
  fromSMT = SMTArray

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
      eval expr >>= share >>= setRef name

  verifyInstr instr@(GetRef (RefComp refName)) (ValComp valName :: Val a) =
    withWitness (undefined :: a) instr $ do
      val <- getRef refName :: Verify (SMTExpr exp a)
      pokeVal valName val

  verifyInstr instr@(SetRef (RefComp name :: Ref a) expr) () =
    withWitness (undefined :: a) instr $ do
      eval expr >>= share >>= setRef name

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
      Dict <- witnessIntegral (undefined :: exp i) =
    withWitness (undefined :: a) instr $ do
      val <- fresh name
      let
        is :: [SMTExpr exp i]
        is = map fromConstant [0..]

        ys :: [SMTExpr exp a]
        ys = map fromConstant xs

        n = fromIntegral (length xs)

      forM_ (zip is ys) $ \(i, x) ->
        assume (select (toSMT val) (toSMT i) `eq` toSMT x)

      poke name (ArrBinding val n :: ArrBinding exp i a)

  verifyInstr instr@(GetArr ix (ArrComp arrName :: Arr i a)) (ValComp valName)
    | Dict <- witnessPred (undefined :: exp i) =
    withWitness (undefined :: a) instr $ do
      arr <- peek arrName :: Verify (ArrBinding exp i a)
      ix  <- eval ix
      val <- share (fromSMT (select (toSMT (arr_value arr)) (toSMT ix)))
      pokeVal valName (val :: SMTExpr exp a)

  verifyInstr instr@(SetArr ix val (ArrComp arrName :: Arr i a)) ()
    | Dict <- witnessPred (undefined :: exp i) =
    withWitness (undefined :: a) instr $ do
      ArrBinding{..} <- peek arrName :: Verify (ArrBinding exp i a)
      ix  <- eval ix
      val <- eval val
      arr_value' <- share (fromSMT (store (toSMT arr_value) (toSMT ix) (toSMT val)))
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
      poke iarrName arr

  verifyInstr instr@(UnsafeThawArr (IArrComp iarrName :: IArr i a)) (ArrComp arrName)
    | Dict <- witnessPred (undefined :: exp i) =
    withWitness (undefined :: a) instr $ do
      arr <- peek iarrName :: Verify (ArrBinding exp i a)
      poke arrName arr

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
    res <- provable (toSMT b)
    if res then
      return (Assert Nothing msg)
    else do
      assume (toSMT b)
      return (Assert (Just cond) msg)
  verifyInstr Break () = do
    break
    return Break
  verifyInstr (If cond t e) () = do
    b <- eval cond
    (t', e') <- ite (toSMT b) (verify t) (verify e)
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
      eval res >>= assume . toSMT
      body' <- verify body
      return (cond', body')
    finished
    return (While cond' body')
  verifyInstr (For range@(lo, step, hi) val@(ValComp name :: Val a) body) ()
    | Dict <- witnessPred (undefined :: exp a),
      Dict <- witnessIntegral (undefined :: exp a),
      Dict <- witnessOrd (undefined :: exp a) = do
      let
        cond = do
          unsafeFreezeRef name name (undefined :: exp a)
          i <- peekVal name
          n <- eval (borderVal hi)
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
      body' <- stack (cond >>= assume >> verify body)
      finished
      return (For range val body')

-- The literals used in predicate abstraction.
data SomeLiteral = forall a. Invariant a => SomeLiteral String (Literal a)

instance Eq SomeLiteral where x == y = compare x y == EQ
instance Ord SomeLiteral where
  compare (SomeLiteral name1 x) (SomeLiteral name2 y) =
    compare name1 name2 `mappend`
    compare (typeOf x) (typeOf y) `mappend`
    case cast y of
      Just y  -> compare x y
      Nothing -> error "weird type error"

instance Show SomeLiteral where show (SomeLiteral name x) = name ++ " " ++ show x

-- Takes a loop body, which should break on exit, and does predicate abstraction.
-- Leaves the verifier in a state which represents an arbitrary loop iteration.
-- Returns a value which when run leaves the verifier in a state where the loop
-- has terminated.
discoverInvariant :: Verify () -> Verify (Verify ())
discoverInvariant body = do
  frame <- findFrame
  abstract frame >>= refine frame
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

    findFrame = stack $ quietly $ noWarn $ do
      -- Put the verifier in an arbitrary state.
      ctx <- get
      forM_ (Map.keys ctx) $ \(Name name (_ :: a)) -> do
        val <- fresh name
        poke name (val :: a)

      -- Run the program and see what changed.
      before <- get
      body
      after  <- get

      return (Map.keys (modified before after))

    refine frame clauses = do
      clauses' <- stack $ quietly $ noWarn $ do
        assumeLiterals frame clauses
        noBreak (breaks body) >>= assume . SMT.not
        fmap (disjunction clauses) (abstract frame)

      if clauses == clauses' then do
        assumeLiterals frame clauses
        return (noBreak (breaks body) >>= assume)
      else refine frame clauses'

    assumeLiterals :: [Name] -> [[SomeLiteral]] -> Verify ()
    assumeLiterals frame clauses = do
      ctx <- get
      forM_ frame $ \(Name name (_ :: a)) -> do
        val <- peek name >>= havoc name
        poke name (val :: a)
      mapM_ (evalClause >=> assume) clauses

    evalClause clause = do
      ctx <- get
      return (disj [ smtLit ctx name lit | SomeLiteral name lit <- clause ])

    abstract frame = fmap (usort . map usort) $ do
      ctx <- get
      res <- quietly $ Abstract.abstract (evalClause >=> provable) (lits frame)
      chat $ liftIO $
        case res of
          [] -> putStrLn ("No invariant found over frame " ++ show frame)
          [clause] -> putStrLn ("Possible invariant " ++ show clause ++ " over frame " ++ show frame)
          _ -> do
            putStrLn ("Possible invariant over frame " ++ show frame ++ ":")
            sequence_ [ putStrLn ("  " ++ show clause) | clause <- res ]
      return res
      where
        lits frame = concat [ map (SomeLiteral name) (literals name x) | Name name x <- frame ]

    disjunction cs1 cs2 =
      prune (usort [ usort (c1 ++ c2) | c1 <- cs1, c2 <- cs2 ])
      where
        prune cs = [ c | c <- cs, and [ c == c' || c' \\ c /= [] | c' <- cs ] ]

    usort :: Ord a => [a] -> [a]
    usort = map head . group . sort
