{-# LANGUAGE DataKinds
           , FlexibleContexts #-}

import Data.Expression
import Data.Map hiding (map)
import Data.Monoid
import Ic3
import RecMc
import Solver

pc  = var "pc"  :: ALia 'IntegralSort
pc' = var "pc'" :: ALia 'IntegralSort

dis = map (DynamicallySorted SIntegralSort) [d0]
dls = map (DynamicallySorted SIntegralSort) [pc]
dos = map (DynamicallySorted SIntegralSort) [d]
d   = var "d"   :: ALia 'IntegralSort
d'  = var "d'"  :: ALia 'IntegralSort
d0  = var "d0"  :: ALia 'IntegralSort
d0' = var "d0'" :: ALia 'IntegralSort

dt = pc .=. 0 .&. pc' .=. 1 .&. d0' .=. d0 .&. d0 .=. d .&. d' .=. d .+. (-1) .|.
     pc .=. 1 .&. pc' .=. 1 .&. d0' .=. d0 .&. d' .=. d

dcs = []

tis = map (DynamicallySorted SIntegralSort) [t0]
tls = map (DynamicallySorted SIntegralSort) [pc]
tos = map (DynamicallySorted SIntegralSort) [t]
t   = var "t"   :: ALia 'IntegralSort
t'  = var "t'"  :: ALia 'IntegralSort
t0  = var "t0"  :: ALia 'IntegralSort
t0' = var "t0'" :: ALia 'IntegralSort

tc1 = var "callT" :: ALia 'BooleanSort

tt = pc .=. 0 .&. pc' .=. 1 .&. t0' .=. t0 .&. t' .=. t .&. t0 .=. t .&. 0 .<.  t .|.
     pc .=. 0 .&. pc' .=. 4 .&. t0' .=. t0 .&. t' .=. t .&. t0 .=. t .&. 0 .>=. t .|.
     pc .=. 1 .&. pc' .=. 2 .&. t0' .=. t0 .&. t' .=. t .+. (-2) .|.
     pc .=. 2 .&. pc' .=. 3 .&. t0' .=. t0 .&. tc1 .|.
     pc .=. 3 .&. pc' .=. 4 .&. t0' .=. t0 .&. t' .=. t .+. 1 .|.
     pc .=. 4 .&. pc' .=. 4 .&. t0' .=. t0 .&. t' .=. t

tcs = [ Call "T" tc1 (t `for` t0 <> t' `for` t) ]

mis = map (DynamicallySorted SIntegralSort) [m0]
mls = map (DynamicallySorted SIntegralSort) [pc]
mos = map (DynamicallySorted SIntegralSort) [m]
m   = var "m"   :: ALia 'IntegralSort
m'  = var "m'"  :: ALia 'IntegralSort
m0  = var "m0"  :: ALia 'IntegralSort
m0' = var "m0'" :: ALia 'IntegralSort

mc1 = var "callT" :: ALia 'BooleanSort
mc2 = var "callD" :: ALia 'BooleanSort

mt = pc .=. 0 .&. pc' .=. 1 .&. m0' .=. m0 .&. m' .=. m .&. m0 .=. m .|.
     pc .=. 1 .&. pc' .=. 2 .&. m0' .=. m0 .&. mc1 .|.
     pc .=. 2 .&. pc' .=. 3 .&. m0' .=. m0 .&. mc2 .|.
     pc .=. 3 .&. pc' .=. 4 .&. m0' .=. m0 .&. mc2 .|.
     pc .=. 4 .&. pc' .=. 4 .&. m0' .=. m0 .&. m' .=. m

mcs = [ Call "T" mc1 (m `for` t0 <> m' `for` t)
      , Call "D" mc2 (m `for` d0 <> m' `for` d) ]

s = fromList . map (\f@(Function n _ _ _ _ _ _ _) -> (n, f)) $ [ Function "M" mis mls mos (pc .=. 0) mt (pc .=. 4) mcs
                                                               , Function "T" tis tls tos (pc .=. 0) tt (pc .=. 4) tcs
                                                               , Function "D" dis dls dos (pc .=. 0) dt (pc .=. 1) dcs ]

cex :: Show (e 'BooleanSort) => Either (Cex e) (Inv e) -> IO ()
cex (Left  (Cex cs)) = putStrLn . ("succeeded with counterexample: " ++) . show $ cs
cex (Right (Inv iv)) = error    . ("failed with invariant: "         ++) . show $ iv

inv :: Show (e 'BooleanSort) => Either (Cex e) (Inv e) -> IO ()
inv (Left  (Cex cs)) = error    . ("failed with counterexample: " ++) . show $ cs
inv (Right (Inv iv)) = putStrLn . ("succeeded with invariant: "   ++) . show $ iv

main = mapM_ (\(sink, p) -> sink =<< runSolver defaultLog ( recmc ic3 "M" (pc .=. 0) p s )) [ (inv, pc .=. 4 .->. m0 .>=. 2 .*. m .+. 4)
                                                                                                 , (cex, pc .=. 4 .->. m0 .<.  2 .*. m .+. 4)
                                                                                                 , (cex, pc .=. 4 .->. m0 .>=. 2 .*. m .+. 5) ]
