-- Wrappers around SMTLib's bitvector types to do signed or unsigned
-- arithmetic.

module Language.Embedded.Verify.Arithmetic where

import Data.Typeable
import Language.SMTLib2 hiding (SMTOrd(..))
import Language.SMTLib2.Internals hiding (SMTOrd(..))
import Language.Embedded.Verify hiding (SMTExpr)

newtype Signed n = Signed (SMTExpr (BitVector (BVTyped n)))
  deriving (Eq, Ord, Num, Typeable)
instance Show (Signed n) where
  show (Signed x) = show x

instance TypeableNat n => Fresh (Signed n) where
  fresh = fmap Signed . fresh

instance TypeableNat n => SMTOrd (Signed n) where
  Signed x .<.  Signed y = bvslt x y
  Signed x .>.  Signed y = bvsgt x y
  Signed x .<=. Signed y = bvsle x y
  Signed x .>=. Signed y = bvsge x y

newtype Unsigned n = Unsigned (SMTExpr (BitVector (BVTyped n)))
  deriving (Eq, Ord, Num, Typeable)
instance Show (Unsigned n) where
  show (Unsigned x) = show x

instance TypeableNat n => Fresh (Unsigned n) where
  fresh = fmap Unsigned . fresh

instance TypeableNat n => SMTOrd (Unsigned n) where
  Unsigned x .<.  Unsigned y = bvult x y
  Unsigned x .>.  Unsigned y = bvugt x y
  Unsigned x .<=. Unsigned y = bvule x y
  Unsigned x .>=. Unsigned y = bvuge x y
