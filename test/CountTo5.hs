{-# LANGUAGE DataKinds
           , FlexibleContexts #-}

import Expression
import Ic3
import Pdr
import Solver
import Prelude hiding (and, or, not, init)

vs      = map (DynamicallySorted SIntegralSort) [pc, i, n]
pc      = var "pc" :: ALia 'IntegralSort
pc'     = var "pc'" :: ALia 'IntegralSort
i       = var "i" :: ALia 'IntegralSort
i'      = var "i'" :: ALia 'IntegralSort
n       = var "n" :: ALia 'IntegralSort
n'      = var "n'" :: ALia 'IntegralSort
t       = pc .=. cnst 0 .&. pc' .=. cnst 1 .&.      i .<. n  .&. i' .=. i .&. n' .=. n .|.
          pc .=. cnst 0 .&. pc' .=. cnst 2 .&. not (i .<. n) .&. i' .=. i .&. n' .=. n .|.
          pc .=. cnst 1 .&. pc' .=. cnst 0 .&. i' .=. i .+. cnst 1 .&. n' .=. n .|.
          pc .=. cnst 2 .&. pc' .=. cnst 2 .&. i' .=. i .&. n' .=. n
init    = pc .=. cnst 0 .&. i .=. cnst 0 .&. n .=. cnst 5 :: ALia 'BooleanSort

cex :: Show (e 'BooleanSort) => Either (Cex e) (Inv e) -> IO ()
cex (Left  (Cex cs)) = putStrLn . ("succeeded with counterexample: " ++) . show $ cs
cex (Right (Inv iv)) = error    . ("failed with invariant: "         ++) . show $ iv

inv :: Show (e 'BooleanSort) => Either (Cex e) (Inv e) -> IO ()
inv (Left  (Cex cs)) = error    . ("failed with counterexample: " ++) . show $ cs
inv (Right (Inv iv)) = putStrLn . ("succeeded with invariant: "   ++) . show $ iv

main = mapM_ (\(sink, p) -> sink =<< runSolver defaultLog ( ic3 vs init t p )) [ (inv, pc .=. cnst 2 .->. not (n .<. i))
                                                                               , (cex, pc .=. cnst 2 .->. i .<. n)
                                                                               , (cex, pc .=. cnst 2 .->. not (cnst 0 .<. i))
                                                                               , (inv, pc .=. cnst 2 .->. not (cnst 5 .<. i))
                                                                               , (cex, pc .=. cnst 2 .->. i .<. cnst 5)
                                                                               , (inv, pc .=. cnst 2 .->. not (cnst 10 .<. i)) ]
