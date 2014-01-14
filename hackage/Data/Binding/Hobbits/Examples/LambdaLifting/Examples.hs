-- |
-- Module      : Data.Binding.Hobbits.SuperComb
-- Copyright   : (c) 2011 Edwin Westbrook, Nicolas Frisby, and Paul Brauner
--
-- License     : BSD3
--
-- Maintainer  : emw4@rice.edu
-- Stability   : experimental
-- Portability : GHC
--

module Data.Binding.Hobbits.Examples.LambdaLifting.Examples where

import Data.Binding.Hobbits.Examples.LambdaLifting.Terms
import Data.Binding.Hobbits

------------------------------------------------------------
-- examples
------------------------------------------------------------

ex1 :: Term ((b1 -> b) -> b1 -> b)
ex1 = lam (\f -> (lam $ \x -> App f x))

ex2 :: Term ((((b2 -> b1) -> b2 -> b1) -> b) -> b)
ex2 = lam (\f1 -> App f1 (lam (\f2 -> lam (\x -> App f2 x))))

ex3 :: Term (b3 -> (((b3 -> b2 -> b1) -> b2 -> b1) -> b) -> b)
ex3 = lam (\x -> lam (\f1 -> App f1 (lam (\f2 -> lam (\y -> f2 `App` x `App` y)))))

ex4
  :: Term
       (((b1 -> b) -> b2 -> b)
        -> (((b1 -> b) -> b2 -> b) -> b2 -> b1)
        -> b2
        -> b1)
ex4 = lam $ \x -> lam $ \f1 ->
      App f1 (lam $ \f2 -> lam $ \y -> f2 `App` (f1 `App` x `App` y))

ex5 :: Term (((b2 -> b1) -> b) -> (b2 -> b1) -> b)
ex5 = lam (\f1 -> lam $ \f2 -> App f1 (lam $ \x -> App f2 x))

-- lambda-lift with a free variable (use mbLambdaLift)
ex6 :: Binding (L ((b -> b) -> a)) (Term a)
ex6 = nu (\f -> App (Var f) (lam $ \x -> x))

-- lambda-lift with a free variable as part of a lambda's environment
ex7 :: Binding (L ((b2 -> b2) -> b1)) (Term ((b1 -> b) -> b))
ex7 = nu (\f -> lam $ \y -> App y $ App (Var f) (lam $ \x -> x))

-- example from paper's Section 4
exP :: Term (((b1 -> b1) -> b) -> (b1 -> b1) -> b)
exP = lam $ \f -> lam $ \g -> App f $ lam $ \x -> App g $ App g x
