module Test where
import qualified Data.Vector.Unboxed as V
import qualified Data.Map as M
import Test.QuickCheck

permutationEquation :: [Int] -> [Int]
permutationEquation input = map solveOne [1..n]
  where
    n = length input
    m = M.fromList $ zip input [1..]
    inv x = M.findWithDefault (error "unexpected") x m
    solveOne x = inv (inv x)

permutationEquationV :: [Int] -> [Int]
permutationEquationV input = V.toList (V.map (+1) solveOne)
      where
        n = length input
        m :: V.Vector Int
        m = V.update (V.replicate n 0) (V.fromList (zip (fmap pred input) [0..]))
        solveOne = V.backpermute m m
