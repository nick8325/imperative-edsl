-- A thin layer on top of simple-smt.
module Language.Embedded.Verify.SMT(
  module Language.Embedded.Verify.SMT,
  module SimpleSMT) where

import Control.Monad.State.Strict
import qualified SimpleSMT as SMT
import SimpleSMT(SExpr(..), Result(..), Value(..), bool, fun, fam, ite, eq, tBool, tInt, tArray, tBits, tReal, select, store, bvULt, bvULeq, bvSLt, bvSLeq, concat, extract, bvNeg, bvAdd, bvSub, bvMul, bvUDiv, bvURem, bvSDiv, bvSRem, bvAnd, bvOr, bvNot, bvXOr, bvShl, bvAShr, bvLShr, signExtend, zeroExtend, real, add, sub, mul, neg, abs, lt, leq, gt, geq, realDiv, int, newLogger)
import Control.Applicative

type SMT = StateT SMTState IO
data SMTState =
  SMTState {
    st_solver :: SMT.Solver,
    st_next   :: Integer }

runZ3 :: [String] -> SMT a -> IO a
runZ3 args m = do
  solver <- SMT.newSolver "z3" (["-smt2", "-in"] ++ args) Nothing
  evalStateT m (SMTState solver 0)

freshNum :: SMT Integer
freshNum = do
  st <- get
  put st { st_next = st_next st + 1 }
  return (st_next st)

withSolver :: (SMT.Solver -> SMT a) -> SMT a
withSolver k = do
  st <- get
  k (st_solver st)

stack :: SMT a -> SMT a
stack m = withSolver $ \solver ->
  lift (SMT.push solver) *> m <* lift (SMT.pop solver)

not :: SExpr -> SExpr
not p
  | p == bool True  = bool False
  | p == bool False = bool True
  | otherwise = SMT.not p

conj :: [SExpr] -> SExpr
conj xs | bool False `elem` xs = bool False
conj [] = bool True
conj [x] = x
conj xs = fun "and" xs

disj :: [SExpr] -> SExpr
disj xs | bool True `elem` xs = bool True
disj [] = bool False
disj [x] = x
disj xs = fun "or" xs

(.||.), (.&&.) :: SExpr -> SExpr -> SExpr
x .||. y = disj [x, y]
x .&&. y = conj [x, y]

setOption :: String -> String -> SMT ()
setOption opt val = withSolver $ \solver ->
  lift (SMT.setOption solver opt val)

getExpr :: SExpr -> SMT Value
getExpr exp = withSolver $ \solver ->
  lift (SMT.getExpr solver exp)

assert :: SExpr -> SMT ()
assert expr = withSolver $ \solver ->
  lift (SMT.assert solver expr)

check :: SMT Result
check = withSolver $ \solver ->
  lift (SMT.check solver)

declare :: String -> SExpr -> SMT SExpr
declare name ty = withSolver $ \solver ->
  lift (SMT.declare solver name ty)

declareFun :: String -> [SExpr] -> SExpr -> SMT SExpr
declareFun name args res = withSolver $ \solver ->
  lift (SMT.declareFun solver name args res)

showSExpr :: SExpr -> String
showSExpr exp = SMT.showsSExpr exp ""

showValue :: Value -> String
showValue (Bool x)   = show x
showValue (Int x)    = show x
showValue (Real x)   = show x
showValue (Bits _ x) = show x
showValue (Other x)  = showSExpr x

getArray :: Value -> SExpr -> SMT [Value]
getArray n arr =
  sequence [ getExpr (select arr i) | i <- indexes n ]
  where
    indexes (Int n) = map int [0..n-1]
    indexes (Bits w n) = map (bits w) [0..n-1]

bits :: Int -> Integer -> SExpr
bits w n =
  List [Atom "_", Atom ("bv" ++ show m), int (fromIntegral w)]
  where
    m = n `mod` (2^w)
