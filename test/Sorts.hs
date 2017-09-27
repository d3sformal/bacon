{-# LANGUAGE DataKinds
           , FlexibleContexts #-}

import Data.Expression
import Data.List hiding (and)
import Data.Maybe
import Data.Singletons
import TwoCellIc3
import Language.Haskell.TH.Syntax
import Prelude hiding (and)
import Solver

pc   = var "pc"   :: ALia 'IntegralSort
d    = var "d"    :: ALia 'IntegralSort
h    = var "h"    :: ALia 'IntegralSort
p    = var "p"    :: ALia 'IntegralSort
b    = var "b"    :: ALia 'IntegralSort
f    = var "f"    :: ALia 'IntegralSort
i    = var "i"    :: ALia 'IntegralSort
x    = var "x"    :: ALia 'IntegralSort
y    = var "y"    :: ALia 'IntegralSort
k1   = var "k1"   :: ALia 'IntegralSort
k2   = var "k2"   :: ALia 'IntegralSort
ak1  = var "ak1"  :: ALia 'IntegralSort
ak2  = var "ak2"  :: ALia 'IntegralSort

a_k1   = var "A.k1"   :: ALia 'IntegralSort
a_k2   = var "A.k2"   :: ALia 'IntegralSort
a_ak1  = var "A.ak1"  :: ALia 'IntegralSort
a_ak2  = var "A.ak2"  :: ALia 'IntegralSort

b_k1   = var "B.k1"   :: ALia 'IntegralSort
b_k2   = var "B.k2"   :: ALia 'IntegralSort
b_ak1  = var "B.ak1"  :: ALia 'IntegralSort
b_ak2  = var "B.ak2"  :: ALia 'IntegralSort

c_k1   = var "C.k1"   :: ALia 'IntegralSort
c_k2   = var "C.k2"   :: ALia 'IntegralSort
c_ak1  = var "C.ak1"  :: ALia 'IntegralSort
c_ak2  = var "C.ak2"  :: ALia 'IntegralSort

pc'  = prime pc
d'   = prime d
h'   = prime h
p'   = prime p
b'   = prime b
f'   = prime f
i'   = prime i
x'   = prime x
y'   = prime y
k1'  = prime k1
k2'  = prime k2
ak1' = prime ak1
ak2' = prime ak2

a_k1'  = prime a_k1
a_k2'  = prime a_k2
a_ak1' = prime a_ak1
a_ak2' = prime a_ak2

b_k1'  = prime b_k1
b_k2'  = prime b_k2
b_ak1' = prime b_ak1
b_ak2' = prime b_ak2

c_k1'  = prime c_k1
c_k2'  = prime c_k2
c_ak1' = prime c_ak1
c_ak2' = prime c_ak2

a  = var "a" :: ALia ('ArraySort 'IntegralSort 'IntegralSort)
a' = prime a

prime = (`substitute` Substitution (\v -> case match v of { Just (Var n s) -> Just . inject $ Var (n ++ "'") s; _ -> Nothing }))

prev :: [ALia 'IntegralSort] -> [ALia 'IntegralSort] -> [(ALia 'IntegralSort, ALia 'IntegralSort)]
prev = flip zip

constant :: [(ALia 'IntegralSort, ALia 'IntegralSort)] -> [ALia 'IntegralSort] -> ALia 'BooleanSort
constant prev vs' = fromMaybe false (and <$> mapM (\v' -> (v' .=.) <$> v' `lookup` prev) vs')

frame :: [ALia 'IntegralSort] -> ALia 'BooleanSort -> ALia 'BooleanSort
frame vs f = let vs' = map prime vs in f .&. constant (prev vs vs') (vs' \\ map (\(IFix (Var v s)) -> inject (Var v s)) (mapMaybe toStaticallySorted (vars f)))

-- Selection sort
--
-- assume:
--   h >= 2             -- empty and singleton arrays are trivially sorted, there cannot be two distinct distinguished cells in such arrays
--   0 <= k1 < k2 < h   -- distinguish two cells
--
-- 0: while (d < h - cnst 1) -- outerloop
--      p := d
--      b := a[d]
--      f := b
--      i := d + cnst 1
-- 1:   while (i < h)   -- innerloop
--        x := a[i]
-- 2:     if (x < b)    -- new minimum
--          b := x
--          p := i
--        i := i + cnst 1
-- 3:   a[d] := b       -- swap
-- 4:   a[p] := f
--      d := d + cnst 1
--
-- assert:
--   forall k l. k < l => a[k] <= a[l] -- sortedness
--
selvs = [ pc, d, h, p, b, f, i, x, k1, k2, ak1, ak2 ]
seli  = pc .=. cnst 0 .&. h .>=. cnst 2 .&. d .=. cnst 0 .&. cnst 0 .<=. k1 .&. k1 .<. k2 .&. k2 .<. h
selp  = pc .=. cnst 5 .->. ak1 .<=. ak2
selt  = k1' .<. k2' .&. (
        -- outer (walk over entire array (prefix is sorted))
        frame selvs ( pc .=. cnst 0 .&. pc' .=. cnst 5 .&. d .>=. h .+. cnst (-1) ) .|.
        frame selvs ( pc .=. cnst 0 .&. pc' .=. cnst 1 .&. d .<.  h .+. cnst (-1) .&. p' .=. d
                                    .&.  (  d .<. a_k1               .&. a_k1 .=. c_k2 .&. a_ak1 .=. c_ak2 .&. a_k2 .=. b_k2 .&. a_ak2 .=. b_ak2 .&. d .=. b_k1 .&. b_k1 .=. c_k1 .&. b_ak1 .=. c_ak1 .&. b' .=. b_ak1 .&. k1' .=. a_k1 .&. ak1' .=. a_ak1 .&. k2' .=. a_k2 .&. ak2' .=. a_ak2 -- d < k1 < k2
                                        .|. b_k1 .<. d .&. d .<. b_k2 .&. d .=. a_k1 .&. a_k1 .=. c_k2 .&. a_ak1 .=. c_ak2 .&. a_k2 .=. b_k2 .&. a_ak2 .=. b_ak2 .&. b_k1 .=. c_k1 .&. b_ak1 .=. c_ak1 .&. b' .=. a_ak1 .&. k1' .=. b_k1 .&. ak1' .=. b_ak1 .&. k2' .=. b_k2 .&. ak2' .=. b_ak2 -- k1 < d < k2
                                        .|. c_k2 .<. d               .&. a_k1 .=. c_k2 .&. a_ak1 .=. c_ak2 .&. a_k2 .=. b_k2 .&. a_ak2 .=. b_ak2 .&. b_k1 .=. c_k1 .&. b_ak1 .=. c_ak1 .&. d .=. b_k2 .&. b' .=. a_ak2 .&. k1' .=. c_k1 .&. ak1' .=. c_ak1 .&. k2' .=. c_k2 .&. ak2' .=. c_ak2 -- k1 < k2 < d
                                        .|. d .=. a_k1               .&. b' .=. a_ak1 .&. k1' .=. a_k1 .&. ak1' .=. a_ak1 .&. k2' .=. a_k2 .&. ak2' .=. a_ak2                                                                                                                     -- d = k1 < k2
                                        .|. d .=. a_k2               .&. b' .=. a_ak2 .&. k1' .=. a_k1 .&. ak1' .=. a_ak1 .&. k2' .=. a_k2 .&. ak2' .=. a_ak2 )                                                                                                                   -- k1 < k2 = d
                                    .&. f' .=. b' .&. i' .=. d .+. cnst 1 ) .|.

        -- inner (find minimum in remainder to be swapped with leftmost element)
        frame selvs ( pc .=. cnst 1 .&. pc' .=. cnst 3 .&. i .>=. h ) .|.
        frame selvs ( pc .=. cnst 1 .&. pc' .=. cnst 2 .&. i .<.  h
                                    .&.  (  i .<. a_k1               .&. a_k1 .=. c_k2 .&. a_ak1 .=. c_ak2 .&. a_k2 .=. b_k2 .&. a_ak2 .=. b_ak2 .&. i .=. b_k1 .&. b_k1 .=. c_k1 .&. b_ak1 .=. c_ak1 .&. x' .=. b_ak1 .&. k1' .=. a_k1 .&. ak1' .=. a_ak1 .&. k2' .=. a_k2 .&. ak2' .=. a_ak2 -- i < k1 < k2
                                        .|. b_k1 .<. i .&. i .<. b_k2 .&. i .=. a_k1 .&. a_k1 .=. c_k2 .&. a_ak1 .=. c_ak2 .&. a_k2 .=. b_k2 .&. a_ak2 .=. b_ak2 .&. b_k1 .=. c_k1 .&. b_ak1 .=. c_ak1 .&. x' .=. a_ak1 .&. k1' .=. b_k1 .&. ak1' .=. b_ak1 .&. k2' .=. b_k2 .&. ak2' .=. b_ak2 -- k1 < i < k2
                                        .|. c_k2 .<. i               .&. a_k1 .=. c_k2 .&. a_ak1 .=. c_ak2 .&. a_k2 .=. b_k2 .&. a_ak2 .=. b_ak2 .&. b_k1 .=. c_k1 .&. b_ak1 .=. c_ak1 .&. i .=. b_k2 .&. x' .=. a_ak2 .&. k1' .=. c_k1 .&. ak1' .=. c_ak1 .&. k2' .=. c_k2 .&. ak2' .=. c_ak2 -- k1 < k2 < i
                                        .|. i .=. a_k1               .&. x' .=. a_ak1 .&. k1' .=. a_k1 .&. ak1' .=. a_ak1 .&. k2' .=. a_k2 .&. ak2' .=. a_ak2                                                                                                                     -- i = k1 < k2
                                        .|. i .=. a_k2               .&. x' .=. a_ak2 .&. k1' .=. a_k1 .&. ak1' .=. a_ak1 .&. k2' .=. a_k2 .&. ak2' .=. a_ak2 ) ) .|.                                                                                                             -- k1 < k2 = i

        -- if (found new minimum, remember value, and index)
        frame selvs ( pc .=. cnst 2 .&. pc' .=. cnst 1 .&. x .>=. b .&. i' .=. i .+. cnst 1 ) .|.
        frame selvs ( pc .=. cnst 2 .&. pc' .=. cnst 1 .&. x .<.  b .&. b' .=. x .&. p' .=. i .&. i' .=. i .+. cnst 1 ) .|.

        -- swap minimum with leftmost
        frame selvs ( pc .=. cnst 3 .&. pc' .=. cnst 4 .&.  (  d ./=. a_k1 .&. d ./=. a_k2 .&. k1' .=. a_k1 .&. ak1' .=. a_ak1 .&. k2' .=. a_k2' .&. ak2' .=. a_ak2
                                                           .|. d .=. a_k1 .&. k1' .=. a_k1 .&. ak1' .=. b .&. k2' .=. a_k2 .&. ak2' .=. a_ak2
                                                           .|. d .=. a_k2 .&. k1' .=. a_k1 .&. ak1' .=. a_ak1 .&. k2' .=. a_k2 .&. ak2' .=. b ) ) .|.
        frame selvs ( pc .=. cnst 4 .&. pc' .=. cnst 0 .&.  (  p ./=. a_k1 .&. p ./=. a_k2 .&. k1' .=. a_k1 .&. ak1' .=. a_ak1 .&. k2' .=. a_k2' .&. ak2' .=. ak2
                                                           .|. p .=. a_k1 .&. k1' .=. a_k1 .&. ak1' .=. f .&. k2' .=. a_k2 .&. ak2' .=. ak2
                                                           .|. p .=. a_k2 .&. k1' .=. a_k1 .&. ak1' .=. a_ak1 .&. k2' .=. a_k2 .&. ak2' .=. f ) .&. d' .=. d .+. cnst 1 ) .|.

        -- end
        frame selvs ( pc .=. cnst 5 )
    )

-- Bubble sort
--
-- 0: while (1 < h)
--      i := 0
-- 1:   while (i < h - 1)
--        x := a[i]
-- 2:     y := a[i+1]
-- 3:     if (x > y)
--          a[i]   := y
-- 4:       a[i+1] := x
--        i := i + 1
--      h := h - 1
--
--  assert:
--    forall k l. k < l => a[k] <= a[l]
--
bubvs = [ pc, h, i, x, y, k1, k2, ak1, ak2 ]
bubi  = pc .=. cnst 0 .&. h .>=. cnst 2 .&. cnst 0 .<=. k1 .&. k1 .<. k2 .&. k2 .<. h
bubp  = pc .=. cnst 5 .->. ak1 .<=. ak2
bubt  = k1' .<. k2' .&. (
        frame bubvs ( pc .=. cnst 0 .&. pc' .=. cnst 4 .&. cnst 1 .>=. h ) .|.
        frame bubvs ( pc .=. cnst 0 .&. pc' .=. cnst 1 .&. cnst 1 .<.  h .&. i' .=. cnst 0 ) .|.

        frame bubvs ( pc .=. cnst 1 .&. pc' .=. cnst 0 .&. i .>=. h .+. cnst (-1) .&. h' .=. h .+. cnst (-1) ) .|.
        frame bubvs ( pc .=. cnst 1 .&. pc' .=. cnst 2 .&. i .<.  h .+. cnst (-1) .&.  (  i .<. k1              .&. k1' .=. i .&. ak1' .=. x' .&. ( k2' .=. k1 .&. ak2' .=. ak1 .|. k2' .=. k2 .&. ak2' .=. ak2 )                               -- i < k1 < k2
                                                                                      .|. k1 .<. i .&. i .<. k2 .&. ( k1' .=. i .&. ak1' .=. x' .&. k2' .=. k2 .&. ak2' .=. ak2 .|. k1' .=. k1 .&. ak1' .=. ak1 .&. k2' .=. i .&. ak2' .=. x' ) -- k1 < i < k2
                                                                                      .|. k2 .<. i              .&. k2' .=. i .&. ak2' .=. x' .&. ( k1' .=. k1 .&. ak1' .=. ak1 .|. k1' .=. k2 .&. ak1' .=. ak1 )                               -- k1 < k2 < i
                                                                                      .|. i .=. k1              .&. k1' .=. k1 .&. k1' .=. i .&. ak1' .=. ak1 .&. ak1' .=. x' .&. k2' .=. k2 .&. ak2' .=. ak2                                   -- i = k1 < k2
                                                                                      .|. i .=. k2              .&. k1' .=. k1 .&. ak1' .=. ak1 .&. k2' .=. k2 .&. k2' .=. i .&. ak2' .=. ak2 .&. ak2' .=. x' ) ) .|.                           -- k1 < k2 = i

        frame bubvs ( pc .=. cnst 2 .&. pc' .=. cnst 3 .&.  (  i .+. cnst 1 .<. k1                         .&. k1' .=. i .+. cnst 1 .&. ak1' .=. y' .&. ( k2' .=. k1 .&. ak2' .=. ak1 .|. k2' .=. k2 .&. ak2' .=. ak2 )                               -- i+1 < k1 < k2
                                                           .|. k1 .<. i .+. cnst 1 .&. i .+. cnst 1 .<. k2 .&. ( k1' .=. i .+. cnst 1 .&. ak1' .=. y' .&. k2' .=. k2 .&. ak2' .=. ak2 .|. k1' .=. k1 .&. ak1' .=. ak1 .&. k2' .=. i .&. ak2' .=. y' ) -- k1 < i+1 < k2
                                                           .|. k2 .<. i .+. cnst 1                         .&. k2' .=. i .+. cnst 1 .&. ak2' .=. y' .&. ( k1' .=. k1 .&. ak1' .=. ak1 .|. k1' .=. k2 .&. ak1' .=. ak1 )                               -- k1 < k2 < i+1
                                                           .|. i .+. cnst 1 .=. k1                         .&. k1' .=. k1 .&. k1' .=. i .+. cnst 1 .&. ak1' .=. ak1 .&. ak1' .=. y' .&. k2' .=. k2 .&. ak2' .=. ak2                                   -- i+1 = k1 < k2
                                                           .|. i .+. cnst 1 .=. k2                         .&. k1' .=. k1 .&. ak1' .=. ak1 .&. k2' .=. k2 .&. k2' .=. i .+. cnst 1 .&. ak2' .=. ak2 .&. ak2' .=. y' ) ) .|.                           -- k1 < k2 = i+1

        frame bubvs ( pc .=. cnst 3 .&. pc' .=. cnst 1 .&. x .<=. y .&. i' .=. i .+. cnst 1 ) .|.
        frame bubvs ( pc .=. cnst 3 .&. pc' .=. cnst 4 .&. x .>.  y .&. ( i ./=. k1 .&. i ./=. k2 .&. ak1' .=. ak1 .&. ak2' .=. ak2 .|. i .=. k1 .&. ak1' .=. y .&. ak2' .=. ak2 .|. i .=. k2 .&. ak1' .=. ak1 .&. ak2' .=. y ) ) .|.

        frame bubvs ( pc .=. cnst 4 .&. pc' .=. cnst 1 .&. ( i .+. cnst 1 ./=. k1 .&. i .+. cnst 1 ./=. k2 .&. ak1' .=. ak1 .&. ak2' .=. ak2 .|. i .+. cnst 1 .=. k1 .&. ak1' .=. x .&. ak2' .=. ak2 .&. i .+. cnst 1 .=. k2 .&. ak1' .=. ak1 .&. ak2' .=. x ) .&. i' .=. i .+. cnst 1 ) .|.

        frame bubvs ( pc .=. cnst 5 )
    )

main1 = runSolver defaultLog ( ic3 (map (DynamicallySorted sing) selvs) seli selt selp )
main2 = runSolver defaultLog ( ic3 (map (DynamicallySorted sing) bubvs) bubi bubt bubp )

main = main1
