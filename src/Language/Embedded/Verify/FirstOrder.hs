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

----------------------------------------------------------------------
-- The main API.
----------------------------------------------------------------------

-- A program, represented without lambdas.
data Prog prog fs a where
  Return :: a -> Prog prog fs a
  Bind :: b -> prog '(Prog prog fs, fs) b -> Prog prog fs a -> Prog prog fs a

-- Transform a program into its lambda-free form.
defunctionalise :: Defunctionalise prog => Program prog fs a -> Prog (FirstOrder prog) fs a
defunctionalise prog = runSupply (defunctionaliseM prog)

-- Icky: given a Program, and a Prog which was generated from it and
-- has been modified, copy the changes over to the Program.
-- The two arguments must have the same structure and the same type of
-- instruction at each position. What "copy the changes" means depends
-- on the types; for the verification backend, it means removing from the
-- Program any assertions that have been marked proved in the Prog.
-- (This function exists because I don't know how to refunctionalise a Prog.)
patch :: (Patch prog, PatchConstraint prog prog) => Prog (FirstOrder prog) fs a -> Program prog fs a -> Program prog fs a
patch (Return _) prog = prog
patch (Bind _ instr rest) prog =
  case view prog of
    instr' :>>= k -> do
      x <- patchInstr instr instr'
      patch rest (k x)

----------------------------------------------------------------------
-- A typeclass for defunctionalisation.
----------------------------------------------------------------------

class (HFunctor instr, DryInterp instr, HTraversable (FirstOrder instr)) => Defunctionalise (instr :: (* -> *, k) -> * -> *) where
  -- The first-order version of the instruction.
  type FirstOrder instr :: (* -> *, k) -> * -> *
  type FirstOrder instr = instr

  -- Defunctionalise an instruction, inside a name supply monad.
  defuncInstr :: MonadSupply m => instr '(prog, fs) a -> m (FirstOrder instr '(prog, fs) a)
  default defuncInstr :: (FirstOrder instr ~ instr, MonadSupply m) => instr '(prog, fs) a -> m (FirstOrder instr '(prog, fs) a)
  defuncInstr = return

instance (Defunctionalise instr1, Defunctionalise instr2) => Defunctionalise (instr1 :+: instr2) where
  type FirstOrder (instr1 :+: instr2) = FirstOrder instr1 :+: FirstOrder instr2
  defuncInstr (Inl x) = fmap Inl (defuncInstr x)
  defuncInstr (Inr x) = fmap Inr (defuncInstr x)

defunctionaliseM :: Defunctionalise prog => Program prog fs a -> Supply (Prog (FirstOrder prog) fs a)
defunctionaliseM prog =
  case view prog of
    Op.Return x -> return (Return x)
    x Op.:>>= k -> do
      name <- dryInterp x
      y <- defuncInstr x >>= htraverse defunctionaliseM
      rest <- defunctionaliseM (k name)
      return (Bind name y rest)
  
instance Defunctionalise RefCMD
instance Defunctionalise ArrCMD
instance Defunctionalise PtrCMD
instance Defunctionalise FileCMD
instance Defunctionalise C_CMD
instance Defunctionalise ChanCMD
instance Defunctionalise ThreadCMD

----------------------------------------------------------------------
-- A typeclass for patching/refunctionalisation.
----------------------------------------------------------------------

class Defunctionalise instr => Patch (instr :: (* -> *, k) -> * -> *) where
  -- Extra constraints, needed in the instance for Patch (f :+: g).
  type PatchConstraint instr (prog :: (* -> *, k) -> * -> *) :: Constraint
  type PatchConstraint instr prog = (instr :<: prog, Patch prog)

  patchInstr :: (PatchConstraint instr prog, PatchConstraint prog prog) => FirstOrder instr '(Prog (FirstOrder prog) fs, fs) a -> instr '(Program prog fs, fs) b -> Program prog fs b

  default patchInstr :: (instr :<: prog) => FirstOrder instr '(Prog (FirstOrder prog) fs, fs) a -> instr '(Program prog fs, fs) b -> Program prog fs b
  patchInstr _ x = singleInj x

instance (Patch instr1, Patch instr2) => Patch (instr1 :+: instr2) where
  type PatchConstraint (instr1 :+: instr2) prog = (PatchConstraint instr1 prog, PatchConstraint instr2 prog)
  patchInstr (Inl x) (Inl y) = patchInstr x y
  patchInstr (Inr x) (Inr y) = patchInstr x y

instance Patch RefCMD
instance Patch ArrCMD
instance Patch PtrCMD
instance Patch FileCMD
instance Patch C_CMD
instance Patch ChanCMD
instance Patch ThreadCMD

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
  If     :: exp Bool -> prog () -> prog () -> ControlCMD (Param3 prog exp pred) ()
  While  :: prog (exp Bool) -> prog () -> ControlCMD (Param3 prog exp pred) ()
  For    :: (pred i, Integral i) => IxRange (exp i) -> Val i -> prog () -> ControlCMD (Param3 prog exp pred) ()
  Break  :: ControlCMD (Param3 prog exp pred) ()
  -- The assertion turns into Nothing if it's proved
  Assert :: Maybe (exp Bool) -> String -> ControlCMD (Param3 prog exp pred) ()

instance HFunctor ControlCMD where
  hfmap f instr = runIdentity (htraverse (pure . f) instr)

instance HTraversable ControlCMD where
  htraverse f (If cond t e) = liftA2 (If cond) (f t) (f e)
  htraverse f (While cond body) = liftA2 While (f cond) (f body)
  htraverse f (For range x body) = fmap (For range x) (f body)
  htraverse _ Break = pure Break
  htraverse _ (Assert cond msg) = pure (Assert cond msg)

instance Defunctionalise CMD.ControlCMD where
  type FirstOrder CMD.ControlCMD = ControlCMD
  defuncInstr (CMD.If cond t f) = return (If cond t f)
  defuncInstr (CMD.While cond body) = return (While cond body)
  defuncInstr (CMD.For range body) = do
    i <- fmap ValComp (freshStr "v")
    return (For range i (body i))
  defuncInstr CMD.Break = return Break
  defuncInstr (CMD.Assert cond msg) = return (Assert (Just cond) msg)

instance Patch CMD.ControlCMD where
  patchInstr (Assert Nothing _) (CMD.Assert _ _) = return ()

  patchInstr (If _ t' f') (CMD.If cond t f) =
    singleInj $ CMD.If cond (patch t' t) (patch f' f)
  patchInstr (While _ body') (CMD.While cond body) =
    singleInj $ CMD.While cond (patch body' body)
  patchInstr (For _ _ body') (CMD.For range body) =
    singleInj $ CMD.For range (patch body' . body)
  patchInstr Break CMD.Break =
    singleInj CMD.Break
  patchInstr (Assert _ _) (CMD.Assert cond msg) =
    singleInj (CMD.Assert cond msg)
