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
defunctionalise :: Defunctionalise inv prog => inv -> Program prog (Param2 exp pred) a -> Prog (FirstOrder inv prog) (Param2 exp pred) a
defunctionalise inv prog = runSupply (defunctionaliseM inv prog)

-- Transform back into a normal imperative-edsl program.
refunctionalise :: forall inv prog exp pred a. (TypeablePred pred, Defunctionalise inv prog, Substitute exp, SubstPred exp ~ pred, pred Bool) => inv -> Prog (FirstOrder inv prog) (Param2 exp pred) a -> Program prog (Param2 exp pred) a
refunctionalise inv prog = refunctionaliseIn inv Map.empty prog

refunctionaliseIn :: forall inv prog exp pred a. (TypeablePred pred, Defunctionalise inv prog, Substitute exp, SubstPred exp ~ pred, pred Bool) => inv -> Subst -> Prog (FirstOrder inv prog) (Param2 exp pred) a -> Program prog (Param2 exp pred) a
refunctionaliseIn _ _ (Return x) = return x
refunctionaliseIn inv sub (Bind x instr prog) =
  case refuncInstr inv sub instr of
    Skip -> do
      refunctionaliseIn inv sub prog
    Discard instr -> do
      singleton instr
      refunctionaliseIn inv sub prog
    Keep instr -> do
      y <- singleton instr
      refunctionaliseIn inv (extendSubst x y sub) prog

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

class (HFunctor instr, DryInterp instr, HTraversable (FirstOrder inv instr)) => Defunctionalise inv (instr :: (* -> *, (* -> *, (* -> Constraint, *))) -> * -> *) where
  -- The first-order version of the instruction.
  type FirstOrder inv instr :: (* -> *, (* -> *, (* -> Constraint, *))) -> * -> *
  type FirstOrder inv instr = instr

  -- Defunctionalise an instruction, inside a name supply monad.
  defuncInstr :: MonadSupply m => inv -> instr (Param3 prog exp pred) a -> m (FirstOrder inv instr (Param3 prog exp pred) a)
  default defuncInstr :: (FirstOrder inv instr ~ instr, MonadSupply m) => inv -> instr (Param3 prog exp pred) a -> m (FirstOrder inv instr (Param3 prog exp pred) a)
  defuncInstr _ = return

  -- Refunctionalise an instruction.
  refuncInstr :: (Defunctionalise inv prog, TypeablePred pred, Substitute exp, SubstPred exp ~ pred, pred Bool) => inv -> Subst -> FirstOrder inv instr '(Prog (FirstOrder inv prog) (Param2 exp pred), Param2 exp pred) a -> Refunc instr prog exp pred a

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

instance (Defunctionalise inv instr1, Defunctionalise inv instr2) => Defunctionalise inv (instr1 :+: instr2) where
  type FirstOrder inv (instr1 :+: instr2) = FirstOrder inv instr1 :+: FirstOrder inv instr2
  defuncInstr inv (Inl x) = fmap Inl (defuncInstr inv x)
  defuncInstr inv (Inr x) = fmap Inr (defuncInstr inv x)

  refuncInstr inv sub (Inl instr) =
    case refuncInstr inv sub instr of
      Keep instr -> Keep (Inl instr)
      Discard instr -> Discard (Inl instr)
      Skip -> Skip
  refuncInstr inv sub (Inr instr) =
    case refuncInstr inv sub instr of
      Keep instr -> Keep (Inr instr)
      Discard instr -> Discard (Inr instr)
      Skip -> Skip

defunctionaliseM :: Defunctionalise inv prog => inv -> Program prog (Param2 exp pred) a -> Supply (Prog (FirstOrder inv prog) (Param2 exp pred) a)
defunctionaliseM inv prog =
  case view prog of
    Op.Return x -> return (Return x)
    x Op.:>>= k -> do
      name <- dryInterp x
      y <- defuncInstr inv x >>= htraverse (defunctionaliseM inv)
      rest <- defunctionaliseM inv (k name)
      return (Bind name y rest)

instance Defunctionalise inv RefCMD where
  refuncInstr _ sub (NewRef name) = keep (NewRef name)
  refuncInstr _ sub (InitRef name exp) = keep (InitRef name (subst sub exp))
  refuncInstr _ sub (GetRef ref) = keep (GetRef (lookupSubst sub ref))
  refuncInstr _ sub instr@(SetRef ref exp) =
    refunc ref (Discard (SetRef (lookupSubst sub ref) (subst sub exp)))
  refuncInstr _ sub (UnsafeFreezeRef ref) = keep (UnsafeFreezeRef (lookupSubst sub ref))

instance Defunctionalise inv ArrCMD where
  refuncInstr _ sub (NewArr name n) = keep2 (NewArr name (subst sub n))
  refuncInstr _ sub (ConstArr name xs) = keep2 (ConstArr name xs)
  refuncInstr _ sub (GetArr arr i) =
    refunc2 arr (Keep (GetArr (lookupSubst sub arr) (subst sub i)))
  refuncInstr _ sub (SetArr arr i x) =
    refunc2 arr (Discard (SetArr (lookupSubst sub arr) (subst sub i) (subst sub x)))
  refuncInstr _ sub (CopyArr (arr1, i) (arr2, j) n) =
    refunc2 arr1 (Discard (CopyArr (lookupSubst sub arr1, subst sub i) (lookupSubst sub arr2, subst sub j) (subst sub n)))
  refuncInstr _ sub (UnsafeFreezeArr arr) =
    keep2 (UnsafeFreezeArr (lookupSubst sub arr))
  refuncInstr _ sub (UnsafeThawArr iarr) =
    keep2 (UnsafeThawArr (lookupSubst sub iarr))

instance Defunctionalise inv PtrCMD where
  refuncInstr _ sub (SwapPtr x y) =
    Discard (SwapPtr (lookupSubst sub x) (lookupSubst sub y))

instance Defunctionalise inv FileCMD where
  refuncInstr _ sub (FOpen name mode) = Keep (FOpen name mode)
  refuncInstr _ sub (FClose h) = Discard (FClose (lookupSubst sub h))
  refuncInstr _ sub (FEof h) = Keep (FEof (lookupSubst sub h))
  refuncInstr _ sub (FPrintf h msg args) =
    Discard (FPrintf (lookupSubst sub h) msg (map (mapPrintfArg (subst sub)) args))
  refuncInstr _ sub (FGet h) = keep (FGet (lookupSubst sub h))

instance Defunctionalise inv C_CMD where
  refuncInstr = error "Can't refunctionalise C_CMD"
instance Defunctionalise inv ChanCMD where
  refuncInstr = error "Can't refunctionalise ChanCMD"
instance Defunctionalise inv ThreadCMD where
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

data ControlCMD inv fs a where
  If      :: exp Bool -> prog () -> prog () -> ControlCMD inv (Param3 prog exp pred) ()
  While   :: [inv] -> prog (exp Bool) -> prog () -> ControlCMD inv (Param3 prog exp pred) ()
  For     :: (pred i, Integral i) => [inv] -> IxRange (exp i) -> Val i -> prog () -> ControlCMD inv (Param3 prog exp pred) ()
  Break   :: ControlCMD inv (Param3 prog exp pred) ()
  -- The assertion turns into Nothing if it's proved
  Assert  :: Maybe (exp Bool) -> String -> ControlCMD inv (Param3 prog exp pred) ()
  Hint    :: pred a => exp a -> ControlCMD inv (Param3 prog exp pred) ()
  Comment :: String -> ControlCMD inv (Param3 prog exp pred) ()

instance HFunctor (ControlCMD inv) where
  hfmap f instr = runIdentity (htraverse (pure . f) instr)

instance HTraversable (ControlCMD inv) where
  htraverse f (If cond t e) = liftA2 (If cond) (f t) (f e)
  htraverse f (While inv cond body) = liftA2 (While inv) (f cond) (f body)
  htraverse f (For inv range x body) = fmap (For inv range x) (f body)
  htraverse _ Break = pure Break
  htraverse _ (Assert cond msg) = pure (Assert cond msg)
  htraverse _ (Hint exp) = pure (Hint exp)
  htraverse _ (Comment msg) = pure (Comment msg)

instance Defunctionalise inv CMD.ControlCMD where
  type FirstOrder inv CMD.ControlCMD = ControlCMD inv
  defuncInstr _ (CMD.If cond t f) = return (If cond t f)
  defuncInstr _ (CMD.While cond body) = return (While [] cond body)
  defuncInstr _ (CMD.For range body) = do
    i <- fmap ValComp (freshStr "v")
    return (For [] range i (body i))
  defuncInstr _ CMD.Break = return Break
  defuncInstr _ (CMD.Assert cond msg) = return (Assert (Just cond) msg)
  defuncInstr _ (CMD.Hint exp) = return (Hint exp)
  defuncInstr _ (CMD.Comment msg) = return (Comment msg)

  refuncInstr inv sub (If cond t e) =
    Discard (CMD.If (subst sub cond) (refunctionaliseIn inv sub t) (refunctionaliseIn inv sub e))
  refuncInstr inv sub (While _ cond body) =
    Discard (CMD.While (refunctionaliseIn inv sub cond) (refunctionaliseIn inv sub body))
  refuncInstr inv sub (For _ (lo :: exp i, step, hi) x body) =
    refunc x $
    Discard $ CMD.For (subst sub lo, step, fmap (subst sub) hi) $ \y ->
      let sub' = extendSubst x y sub in
      refunctionaliseIn inv sub' body
  refuncInstr _ _ Break = Discard CMD.Break
  refuncInstr _ _ (Assert Nothing msg) =
    Discard (CMD.Comment ("Discharged assertion \"" ++ msg ++ "\""))
  refuncInstr _ sub (Assert (Just cond) msg) = Discard (CMD.Assert (subst sub cond) msg)
  refuncInstr _ sub (Hint exp) = Discard (CMD.Hint (subst sub exp))
  refuncInstr _ sub (Comment msg) = Discard (CMD.Comment msg)
