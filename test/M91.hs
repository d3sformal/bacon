{-# LANGUAGE DataKinds #-}

import Data.Map hiding (map)
import Data.Monoid
import Expression
import Ic3
import RecMc
import Solver
import Prelude hiding (and, or, not, init)

m91is = map (DynamicallySorted SIntegralSort) [n0]
m91ls = map (DynamicallySorted SIntegralSort) [pc]
m91os = map (DynamicallySorted SIntegralSort) [n]

pc  = var "pc"  :: ALia 'IntegralSort
pc' = var "pc'" :: ALia 'IntegralSort
n   = var "n"   :: ALia 'IntegralSort
n'  = var "n'"  :: ALia 'IntegralSort
n0  = var "n0"  :: ALia 'IntegralSort
n0' = var "n0'" :: ALia 'IntegralSort

m91c1 = var "m91c1" :: ALia 'BooleanSort
m91c2 = var "m91c2" :: ALia 'BooleanSort

m91t = pc .=. cnst 0 .&. pc' .=. cnst 3 .&. n0' .=. n0 .&. n0 .=. n .&.      cnst 100 .<. n  .&. n' .=. n .+. cnst (-10) .|.
       pc .=. cnst 0 .&. pc' .=. cnst 1 .&. n0' .=. n0 .&. n0 .=. n .&. not (cnst 100 .<. n) .&. n' .=. n .+. cnst 11 .|.
       pc .=. cnst 1 .&. pc' .=. cnst 2 .&. n0' .=. n0 .&. m91c1 .|.
       pc .=. cnst 2 .&. pc' .=. cnst 3 .&. n0' .=. n0 .&. m91c2 .|.
       pc .=. cnst 3 .&. pc' .=. cnst 3 .&. n0' .=. n0 .&. n' .=. n

m91cs = [ Call "m91" m91c1 (n `for` n0 <> n' `for` n)
        , Call "m91" m91c2 (n `for` n0 <> n' `for` n) ]

s = fromList [ ("m91", Function "m91" m91is m91ls m91os (pc .=. cnst 0) m91t (pc .=. cnst 3) m91cs) ]

cex :: Show (e 'BooleanSort) => Either (Cex e) (Inv e) -> IO ()
cex (Left  (Cex cs)) = putStrLn . ("succeeded with counterexample: " ++) . show $ cs
cex (Right (Inv iv)) = error    . ("failed with invariant: "         ++) . show $ iv

inv :: Show (e 'BooleanSort) => Either (Cex e) (Inv e) -> IO ()
inv (Left  (Cex cs)) = error    . ("failed with counterexample: " ++) . show $ cs
inv (Right (Inv iv)) = putStrLn . ("succeeded with invariant: "   ++) . show $ iv

main = mapM_ (\(sink, i, p) -> sink =<< runSolver defaultLog ( recmc ic3 "m91" i p s )) [ (inv, pc .=. cnst 0, pc .=. cnst 3 .->. cnst  90 .<. n)
                                                                                        , (cex, pc .=. cnst 0, pc .=. cnst 3 .->. cnst 100 .<. n)
                                                                                        , (inv, pc .=. cnst 0 .&. cnst 100 .<. n , pc .=. cnst 3 .->. n0 .=. n .+. cnst 10)
                                                                                        , (inv, pc .=. cnst 0 .&. not (cnst 100 .<. n), pc .=. cnst 3 .->. n  .=. cnst 91) ]
