{-# LANGUAGE DataKinds
           , FlexibleContexts
           , RankNTypes
           , TypeOperators #-}

import Expression
import QIc3 -- Make sure to use Quantifier-aware Ic3
import Pdr
import Solver

-- All variables used in the system to be analyzed by IC3
vs  = map (DynamicallySorted SIntegralSort) [pc, i, j, v] ++ [DynamicallySorted (SArraySort SIntegralSort SIntegralSort) a]

-- Pre and Post state variables (of type Int)
pc  = var "pc"  :: ALia 'IntegralSort
pc' = var "pc'" :: ALia 'IntegralSort
i   = var "i"   :: ALia 'IntegralSort
i'  = var "i'"  :: ALia 'IntegralSort
j   = var "j"   :: ALia 'IntegralSort
j'  = var "j'"  :: ALia 'IntegralSort
v   = var "v"   :: ALia 'IntegralSort
v'  = var "v'"  :: ALia 'IntegralSort

-- Pre and Post state variables (of type [Int])
a   = var "a"   :: ALia ('ArraySort 'IntegralSort 'IntegralSort)
a'  = var "a'"  :: ALia ('ArraySort 'IntegralSort 'IntegralSort)

-- The transition relation (Total except for initial conditions (i /= j, i >= 0, j >= 0)
t = pc .=. cnst 0 .&. pc' .=. cnst 1 .&. i ./=. j .&. i .>=. cnst 0 .&. j .>=. cnst 0 .&. i' .=. i .&. j' .=. j .&. v' .=. select a i .&. a' .=. a .|.
    pc .=. cnst 1 .&. pc' .=. cnst 2 .&. i' .=. i .&. j' .=. j .&. v' .=. v .&. a' .=. store a j v .|.
    pc .=. cnst 2 .&. pc' .=. cnst 2 .&. i' .=. i .&. j' .=. j .&. v' .=. v .&. a' .=. a

-- Check expected outcome
cex :: Show (e 'BooleanSort) => Either (Cex e) (Inv e) -> IO ()
cex (Left  (Cex cs)) = putStrLn . ("succeeded with counterexample: " ++) . show $ cs
cex (Right (Inv iv)) = error    . ("failed with invariant: "         ++) . show $ iv

inv :: Show (e 'BooleanSort) => Either (Cex e) (Inv e) -> IO ()
inv (Left  (Cex cs)) = error    . ("failed with counterexample: " ++) . show $ cs
inv (Right (Inv iv)) = putStrLn . ("succeeded with invariant: "   ++) . show $ iv

-- Auxiliary variables for quantified property
k, l :: forall g. VarF :<: g => IFix g 'IntegralSort
k = var "k"
l = var "l"

-- Run ic3 with different properties, check whether ic3 responds with an expected Cex or Inv
main = mapM_ (\(sink, p) -> sink =<< runSolver logAll ( ic3 vs (pc .=. cnst 0) t p )) [ (inv, pc .=. cnst 2 .->. exists [k, l] (k ./=. l .&.  select a k .=.  select a l))
                                                                                      , (cex, pc .=. cnst 2 .->. forall [k, l] (k ./=. l .->. select a k ./=. select a l)) ]
