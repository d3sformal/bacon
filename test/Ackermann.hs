{-# LANGUAGE DataKinds #-}

import Data.Map (singleton)
import Data.Monoid
import Expression
import Ic3
import RecMc
import Solver

ais = map (DynamicallySorted SIntegralSort) [m0, n0]
als = map (DynamicallySorted SIntegralSort) [pc, n]
aos = map (DynamicallySorted SIntegralSort) [r]

pc  = var "pc"  :: ALia 'IntegralSort
pc' = var "pc'" :: ALia 'IntegralSort
m0  = var "m0"  :: ALia 'IntegralSort
m0' = var "m0'" :: ALia 'IntegralSort
n   = var "n"   :: ALia 'IntegralSort
n'  = var "n'"  :: ALia 'IntegralSort
n0  = var "n0"  :: ALia 'IntegralSort
n0' = var "n0'" :: ALia 'IntegralSort
r   = var "r"   :: ALia 'IntegralSort
r'  = var "r'"  :: ALia 'IntegralSort

ac1 = var "ac1" :: ALia 'BooleanSort
ac2 = var "ac2" :: ALia 'BooleanSort
ac3 = var "ac3" :: ALia 'BooleanSort

at = pc .=. cnst 0 .&. pc' .=. cnst 4 .&. m0' .=. m0 .&. n0' .=. n0 .&. m0 .=.  cnst 0 .&. r' .=. n0 .+. cnst 1 .|.
     pc .=. cnst 0 .&. pc' .=. cnst 1 .&. m0' .=. m0 .&. n0' .=. n0 .&. m0 ./=. cnst 0 .&. n0 .=.  cnst 0 .|.
     pc .=. cnst 0 .&. pc' .=. cnst 2 .&. m0' .=. m0 .&. n0' .=. n0 .&. m0 ./=. cnst 0 .&. n0 ./=. cnst 0 .|.
     pc .=. cnst 1 .&. pc' .=. cnst 4 .&. m0' .=. m0 .&. n0' .=. n0 .&. ac1 .|.
     pc .=. cnst 2 .&. pc' .=. cnst 3 .&. m0' .=. m0 .&. n0' .=. n0 .&. ac2 .|.
     pc .=. cnst 3 .&. pc' .=. cnst 4 .&. m0' .=. m0 .&. n0' .=. n0 .&. ac3 .|.
     pc .=. cnst 4 .&. pc' .=. cnst 4 .&. m0' .=. m0 .&. n0' .=. n0 .&. n' .=. n .&. r' .=. r

acs = [ Call "a" ac1 ((m0 .+. cnst (-1)) `for` m0 <>            cnst 1 `for` n0 <> r' `for` r)
      , Call "a" ac2 (                               (n .+. cnst (-1)) `for` n0 <> n' `for` r)
      , Call "a" ac3 ((m0 .+. cnst (-1)) `for` m0 <>                 n `for` n0 <> r' `for` r) ]

s = singleton "a" $ Function "a" ais als aos (pc .=. cnst 0) at (pc .=. cnst 4) acs

cex :: Show (e 'BooleanSort) => Either (Cex e) (Inv e) -> IO ()
cex (Left  (Cex cs)) = putStrLn . ("succeeded with counterexample: " ++) . show $ cs
cex (Right (Inv iv)) = error    . ("failed with invariant: "         ++) . show $ iv

inv :: Show (e 'BooleanSort) => Either (Cex e) (Inv e) -> IO ()
inv (Left  (Cex cs)) = error    . ("failed with counterexample: " ++) . show $ cs
inv (Right (Inv iv)) = putStrLn . ("succeeded with invariant: "   ++) . show $ iv

main = inv =<< runSolver logAll ( recmc ic3 "a" (pc .=. cnst 0 .&. m0 .>=. cnst 0 .&. n0 .>=. cnst 0) (pc .=. cnst 4 .->. cnst 0 .<. r) s )
