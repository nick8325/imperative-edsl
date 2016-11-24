----------------------------------------------------------------------
-- A first-order form for imperative-edsl programs.
----------------------------------------------------------------------

module Language.Embedded.Verify.FirstOrder where

import Data.Constraint
import Data.Functor.Identity
import Control.Applicative
import Control.Monads
import Control.Monad.Operational.Higher hiding (Return, Bind)
import qualified Control.Monad.Operational.Higher as Op
import Language.Embedded.Imperative.CMD hiding (ControlCMD(..))
import qualified Language.Embedded.Imperative.CMD as CMD
import Language.Embedded.Concurrent.CMD
import Language.Embedded.Traversal
import Language.Embedded.Expression
import Data.Maybe
import Data.Monoid
import Data.Typeable
import qualified Data.Map.Strict as Map
import qualified Data.Loc as C
import qualified Language.C.Syntax as C
import qualified Language.C.Quote.C as C
import Data.Constraint

----------------------------------------------------------------------
-- The main API.
----------------------------------------------------------------------

-- A program, represented without lambdas.
data Prog prog fs a where
  Return :: a -> Prog prog fs a
  Bind :: b -> prog '(Prog prog fs, fs) b -> Prog prog fs a -> Prog prog fs a

-- Transform a program into its lambda-free form.
defunctionalise :: Defunctionalise prog => Program prog (Param2 exp pred) a -> Prog (FirstOrder prog) (Param2 exp pred) a
defunctionalise prog = runSupply (defunctionaliseM prog)

-- Transform back into a normal imperative-edsl program.
refunctionalise :: forall prog exp pred a. (TypeablePred pred, Defunctionalise prog, Substitute exp, SubstPred exp ~ pred, pred Bool) => Prog (FirstOrder prog) (Param2 exp pred) a -> Program prog (Param2 exp pred) a
refunctionalise prog = refunctionaliseIn Map.empty prog

refunctionaliseIn :: forall prog exp pred a. (TypeablePred pred, Defunctionalise prog, Substitute exp, SubstPred exp ~ pred, pred Bool) => Subst -> Prog (FirstOrder prog) (Param2 exp pred) a -> Program prog (Param2 exp pred) a
refunctionaliseIn _ (Return x) = return x
refunctionaliseIn sub (Bind x instr prog) =
  case refuncInstr sub instr of
    Skip -> do
      refunctionaliseIn sub prog
    Discard instr -> do
      singleton instr
      refunctionaliseIn sub prog
    Keep instr -> do
      y <- singleton instr
      refunctionaliseIn (extendSubst x y sub) prog

class TypeablePred pred where
  witnessTypeable :: Dict (pred a) -> Dict (Typeable a)

----------------------------------------------------------------------
-- Substitutions.
----------------------------------------------------------------------

type Subst = Map.Map Value Value
data Value = forall a. Typeable a => Value C.Id a
instance Eq Value where
  x == y = compare x y == EQ
instance Ord Value where
  compare (Value nx x) (Value ny y) =
    compare (typeOf x) (typeOf y) `mappend`
    compare nx ny

extendSubst :: (C.ToIdent a, Typeable a) => a -> a -> Subst -> Subst
extendSubst x y sub =
  Map.insert (Value (C.toIdent x C.noLoc) x) (Value (C.toIdent y C.noLoc) y) sub

lookupSubst :: (C.ToIdent a, Typeable a) => Subst -> a -> a
lookupSubst sub x = fromMaybe x $ do
  Value _ y <- Map.lookup (Value (C.toIdent x C.noLoc) x) sub
  return (fromMaybe (error "type error in substitution") (cast y))

class Substitute exp where
  type SubstPred exp :: * -> Constraint
  subst :: SubstPred exp a => Subst -> exp a -> exp a

----------------------------------------------------------------------
-- A typeclass for defunctionalisation and refunctionalisation.
----------------------------------------------------------------------

class (HFunctor instr, DryInterp instr, HTraversable (FirstOrder instr)) => Defunctionalise (instr :: (* -> *, (* -> *, (* -> Constraint, *))) -> * -> *) where
  -- The first-order version of the instruction.
  type FirstOrder instr :: (* -> *, (* -> *, (* -> Constraint, *))) -> * -> *
  type FirstOrder instr = instr

  -- Defunctionalise an instruction, inside a name supply monad.
  defuncInstr :: MonadSupply m => instr (Param3 prog exp pred) a -> m (FirstOrder instr (Param3 prog exp pred) a)
  default defuncInstr :: (FirstOrder instr ~ instr, MonadSupply m) => instr (Param3 prog exp pred) a -> m (FirstOrder instr (Param3 prog exp pred) a)
  defuncInstr = return

  -- Refunctionalise an instruction.
  refuncInstr :: (Defunctionalise prog, TypeablePred pred, Substitute exp, SubstPred exp ~ pred, pred Bool) => Subst -> FirstOrder instr '(Prog (FirstOrder prog) (Param2 exp pred), Param2 exp pred) a -> Refunc instr prog exp pred a

data Refunc instr prog exp pred a where
  Keep    :: (Typeable a, C.ToIdent a) => instr '(Program prog (Param2 exp pred), Param2 exp pred) a -> Refunc instr prog exp pred a
  Discard :: instr '(Program prog (Param2 exp pred), Param2 exp pred) a -> Refunc instr prog exp pred a
  Skip :: Refunc instr prog exp pred a

refunc :: forall f instr prog exp pred a b. (TypeablePred pred, pred a, Typeable f) => f a -> (Typeable a => Refunc instr prog exp pred b) -> Refunc instr prog exp pred b
refunc _ x =
  case witnessTypeable (Dict :: Dict (pred a)) of
    Dict -> x

refunc2 :: forall f instr prog exp pred a b c. (TypeablePred pred, pred a, pred b, Typeable f) => f a b -> ((Typeable a, Typeable b) => Refunc instr prog exp pred c) -> Refunc instr prog exp pred c
refunc2 _ x =
  case (witnessTypeable (Dict :: Dict (pred a)), witnessTypeable (Dict :: Dict (pred b))) of
    (Dict, Dict) -> x

keep :: forall f instr prog exp pred a. (TypeablePred pred, pred a, Typeable f, C.ToIdent (f a)) => (Typeable a => instr '(Program prog (Param2 exp pred), Param2 exp pred) (f a)) -> Refunc instr prog exp pred (f a)
keep x = refunc (undefined :: f a) (Keep x)

keep2 :: forall f instr prog exp pred a b. (TypeablePred pred, pred a, pred b, Typeable f, C.ToIdent (f a b)) => ((Typeable a, Typeable b) => instr '(Program prog (Param2 exp pred), Param2 exp pred) (f a b)) -> Refunc instr prog exp pred (f a b)
keep2 x = refunc2 (undefined :: f a b) (Keep x)

instance (Defunctionalise instr1, Defunctionalise instr2) => Defunctionalise (instr1 :+: instr2) where
  type FirstOrder (instr1 :+: instr2) = FirstOrder instr1 :+: FirstOrder instr2
  defuncInstr (Inl x) = fmap Inl (defuncInstr x)
  defuncInstr (Inr x) = fmap Inr (defuncInstr x)

  refuncInstr sub (Inl instr) =
    case refuncInstr sub instr of
      Keep instr -> Keep (Inl instr)
      Discard instr -> Discard (Inl instr)
      Skip -> Skip
  refuncInstr sub (Inr instr) =
    case refuncInstr sub instr of
      Keep instr -> Keep (Inr instr)
      Discard instr -> Discard (Inr instr)
      Skip -> Skip

defunctionaliseM :: Defunctionalise prog => Program prog (Param2 exp pred) a -> Supply (Prog (FirstOrder prog) (Param2 exp pred) a)
defunctionaliseM prog =
  case view prog of
    Op.Return x -> return (Return x)
    x Op.:>>= k -> do
      name <- dryInterp x
      y <- defuncInstr x >>= htraverse defunctionaliseM
      rest <- defunctionaliseM (k name)
      return (Bind name y rest)

instance Defunctionalise RefCMD where
  refuncInstr sub (NewRef name) = keep (NewRef name)
  refuncInstr sub (InitRef name exp) = keep (InitRef name (subst sub exp))
  refuncInstr sub (GetRef ref) = keep (GetRef (lookupSubst sub ref))
  refuncInstr sub instr@(SetRef ref exp) =
    refunc ref (Discard (SetRef (lookupSubst sub ref) (subst sub exp)))
  refuncInstr sub (UnsafeFreezeRef ref) = keep (UnsafeFreezeRef (lookupSubst sub ref))

instance Defunctionalise ArrCMD where
  refuncInstr sub (NewArr name n) = keep2 (NewArr name (subst sub n))
  refuncInstr sub (ConstArr name xs) = keep2 (ConstArr name xs)
  refuncInstr sub (GetArr arr i) =
    refunc2 arr (Keep (GetArr (lookupSubst sub arr) (subst sub i)))
  refuncInstr sub (SetArr arr i x) =
    refunc2 arr (Discard (SetArr (lookupSubst sub arr) (subst sub i) (subst sub x)))
  refuncInstr sub (CopyArr (arr1, i) (arr2, j) n) =
    refunc2 arr1 (Discard (CopyArr (lookupSubst sub arr1, subst sub i) (lookupSubst sub arr2, subst sub j) (subst sub n)))
  refuncInstr sub (UnsafeFreezeArr arr) =
    keep2 (UnsafeFreezeArr (lookupSubst sub arr))
  refuncInstr sub (UnsafeThawArr iarr) =
    keep2 (UnsafeThawArr (lookupSubst sub iarr))

instance Defunctionalise PtrCMD where
  refuncInstr sub (SwapPtr x y) =
    Discard (SwapPtr (lookupSubst sub x) (lookupSubst sub y))

instance Defunctionalise FileCMD where
  refuncInstr sub (FOpen name mode) = Keep (FOpen name mode)
  refuncInstr sub (FClose h) = Discard (FClose (lookupSubst sub h))
  refuncInstr sub (FEof h) = Keep (FEof (lookupSubst sub h))
  refuncInstr sub (FPrintf h msg args) =
    Discard (FPrintf (lookupSubst sub h) msg (map (mapPrintfArg (subst sub)) args))
  refuncInstr sub (FGet h) = keep (FGet (lookupSubst sub h))

instance Defunctionalise C_CMD where
  refuncInstr = error "Can't refunctionalise C_CMD"
instance Defunctionalise ChanCMD where
  refuncInstr = error "Can't refunctionalise ChanCMD"
instance Defunctionalise ThreadCMD where
  refuncInstr = error "Can't refunctionalise ThreadCMD"

----------------------------------------------------------------------
-- A Traversable-like typeclass and instances.
----------------------------------------------------------------------

class HFunctor instr => HTraversable instr where
  htraverse ::
    Applicative f =>
    (forall a. prog a -> f (prog' a)) ->
    instr '(prog, fs) a ->
    f (instr '(prog', fs) a)

  htraverse _ x =
    pure (hfmap (\_ -> error "compound instruction") x)

instance (HTraversable f, HTraversable g) => HTraversable (f :+: g) where
  htraverse f (Inl x) = fmap Inl (htraverse f x)
  htraverse f (Inr x) = fmap Inr (htraverse f x)

instance HTraversable RefCMD
instance HTraversable ArrCMD
instance HTraversable PtrCMD
instance HTraversable FileCMD
instance HTraversable C_CMD
instance HTraversable ChanCMD
instance HTraversable ThreadCMD

----------------------------------------------------------------------
-- The first-order replacement for ControlCMD.
----------------------------------------------------------------------

data ControlCMD fs a where
  If      :: exp Bool -> prog () -> prog () -> ControlCMD (Param3 prog exp pred) ()
  While   :: prog (exp Bool) -> prog () -> ControlCMD (Param3 prog exp pred) ()
  For     :: (pred i, Integral i) => IxRange (exp i) -> Val i -> prog () -> ControlCMD (Param3 prog exp pred) ()
  Break   :: ControlCMD (Param3 prog exp pred) ()
  -- The assertion turns into Nothing if it's proved
  Assert  :: Maybe (exp Bool) -> String -> ControlCMD (Param3 prog exp pred) ()
  Hint    :: pred a => exp a -> ControlCMD (Param3 prog exp pred) ()
  Comment :: String -> ControlCMD (Param3 prog exp pred) ()

instance HFunctor ControlCMD where
  hfmap f instr = runIdentity (htraverse (pure . f) instr)

instance HTraversable ControlCMD where
  htraverse f (If cond t e) = liftA2 (If cond) (f t) (f e)
  htraverse f (While cond body) = liftA2 While (f cond) (f body)
  htraverse f (For range x body) = fmap (For range x) (f body)
  htraverse _ Break = pure Break
  htraverse _ (Assert cond msg) = pure (Assert cond msg)
  htraverse _ (Hint exp) = pure (Hint exp)
  htraverse _ (Comment msg) = pure (Comment msg)

instance Defunctionalise CMD.ControlCMD where
  type FirstOrder CMD.ControlCMD = ControlCMD
  defuncInstr (CMD.If cond t f) = return (If cond t f)
  defuncInstr (CMD.While cond body) = return (While cond body)
  defuncInstr (CMD.For range body) = do
    i <- fmap ValComp (freshStr "v")
    return (For range i (body i))
  defuncInstr CMD.Break = return Break
  defuncInstr (CMD.Assert cond msg) = return (Assert (Just cond) msg)
  defuncInstr (CMD.Hint exp) = return (Hint exp)
  defuncInstr (CMD.Comment msg) = return (Comment msg)

  refuncInstr sub (If cond t e) =
    Discard (CMD.If (subst sub cond) (refunctionaliseIn sub t) (refunctionaliseIn sub e))
  refuncInstr sub (While cond body) =
    Discard (CMD.While (refunctionaliseIn sub cond) (refunctionaliseIn sub body))
  refuncInstr sub (For (lo :: exp i, step, hi) x body) =
    refunc x $
    Discard $ CMD.For (subst sub lo, step, fmap (subst sub) hi) $ \y ->
      let sub' = extendSubst x y sub in
      refunctionaliseIn sub' body
  refuncInstr _ Break = Discard CMD.Break
  refuncInstr _ (Assert Nothing msg) =
    Discard (CMD.Comment ("Discharged assertion \"" ++ msg ++ "\""))
  refuncInstr sub (Assert (Just cond) msg) = Discard (CMD.Assert (subst sub cond) msg)
  refuncInstr sub (Hint exp) = Discard (CMD.Hint (subst sub exp))
  refuncInstr sub (Comment msg) = Discard (CMD.Comment msg)
