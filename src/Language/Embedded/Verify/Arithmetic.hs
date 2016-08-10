-- Wrappers around SMTLib's bitvector types to do signed or unsigned
-- arithmetic.

module Language.Embedded.Verify.Arithmetic where

import Data.Typeable
import Language.Embedded.Verify hiding (ite)
import Language.Embedded.Verify.SMT
import qualified Language.Embedded.Verify.SMT as SMT

data W8
data W16
data W32
data W64

class Width w where width :: Num a => w -> a
instance Width W8  where width _ = 8
instance Width W16 where width _ = 16
instance Width W32 where width _ = 32
instance Width W64 where width _ = 64

data Signed
data Unsigned

class Sign s where isSigned :: BV s w -> Bool
instance Sign Signed   where isSigned _ = True
instance Sign Unsigned where isSigned _ = False

newtype BV s w = BV { unBV :: SExpr }
  deriving (Eq, Ord, Typeable)
instance Show (BV s a) where
  show (BV x) = show x

instance (Sign s, Width w) => Num (BV s w) where
  fromInteger n = BV (bits (width (undefined :: w)) n)
  BV x + BV y = BV (bvAdd x y)
  BV x - BV y = BV (bvSub x y)

  -- Feldspar uses the idiom b * x (where b is a boolean) to mean
  -- b ? x : 0. But the SMT solver doesn't like multiplication.
  -- Here are some transformations which simplify away that idiom.
  BV (List [Atom "ite", b, x, y]) * z =
    BV (ite b (unBV (BV x * z)) (unBV (BV y * z)))
  x * BV (List [Atom "ite", b, y, z]) =
    BV (ite b (unBV (x * BV y)) (unBV (x * BV z)))
  x * y | x == 0 || y == 0 = 0
  x * y | x == 1 = y
  x * y | y == 1 = x
  BV x * BV y = BV (bvMul x y)
  negate (BV x) = BV (bvNeg x)
  abs = smtAbs
  signum = smtSignum

instance Enum (BV s w) where
  toEnum   = error "no Enum for BV"
  fromEnum = error "no Enum for BV"
instance (Sign s, Width w) => Real (BV s w) where
  toRational = error "no toRational for BV"
instance (Sign s, Width w) => Integral (BV s w) where
  toInteger = error "no toInteger for BV"
  n0@(BV n) `quotRem` BV d
    | isSigned n0 = (BV (bvSDiv n d), BV (bvSRem n d))
    | otherwise   = (BV (bvUDiv n d), BV (bvURem n d))

-- A slightly lighter version of Data.Bits.
class Bits a where
  (.&.), (.|.) :: a -> a -> a
  complement :: a -> a
  xor :: a -> a -> a
  shiftL :: a -> a -> a
  shiftR :: a -> a -> a

instance (Sign s, Width w) => Bits (BV s w) where
  BV x .&. BV y = BV (bvAnd x y)
  BV x .|. BV y = BV (bvOr x y)
  complement (BV x) = BV (bvNot x)
  BV x `xor` BV y = BV (bvXOr x y)
  shiftL (BV x) (BV n) = BV (bvShl x n)
  shiftR x0@(BV x) (BV n)
    | isSigned x0 = BV (bvAShr x n)
    | otherwise   = BV (bvLShr x n)

instance (Sign s, Width w) => SMTOrd (BV s w) where
  x .<. y
    | isSigned x = bvSLt (unBV x) (unBV y)
    | otherwise  = bvULt (unBV x) (unBV y)
  x .<=. y
    | isSigned x = bvSLeq (unBV x) (unBV y)
    | otherwise  = bvULeq (unBV x) (unBV y)
  x .>.  y = y .<.  x
  x .>=. y = y .<=. x

instance (Sign s, Width w) => Fresh (BV s w) where
  fresh = freshSExpr

instance (Sign s, Width w) => TypedSExpr (BV s w) where
  smtType _ = tBits (width (undefined :: w))
  toSMT = unBV
  fromSMT = BV

newtype Rat = Rat { unRat :: SExpr }
  deriving (Eq, Ord, Typeable)
instance Show Rat where
  show (Rat x) = show x

instance Fresh Rat where
  fresh = freshSExpr
instance TypedSExpr Rat where
  smtType _ = tReal
  toSMT = unRat
  fromSMT = Rat

instance Num Rat where
  fromInteger = Rat . real . fromInteger
  Rat x + Rat y = Rat (add x y)
  Rat x - Rat y = Rat (sub x y)
  Rat x * Rat y = Rat (mul x y)
  negate (Rat x) = Rat (neg x)
  abs (Rat x) = Rat (SMT.abs x)
  signum = smtSignum

instance Fractional Rat where
  Rat x / Rat y = Rat (realDiv x y)
  fromRational = Rat . real

instance SMTOrd Rat where
  Rat x .<.  Rat y = lt  x y
  Rat x .<=. Rat y = leq x y
  Rat x .>.  Rat y = gt  x y
  Rat x .>=. Rat y = geq x y

smtAbs :: (Num a, SMTOrd a, TypedSExpr a) => a -> a
smtAbs (x :: a) =
  fromSMT (ite (x .<. 0) (toSMT (negate x)) (toSMT x))

smtSignum :: (Num a, SMTOrd a, TypedSExpr a) => a -> a
smtSignum (x :: a) =
  fromSMT $
    ite (x .<. 0) (toSMT (-1 :: a)) $
    ite (x .>. 0) (toSMT  (1 :: a))
    (toSMT (0 :: a))
