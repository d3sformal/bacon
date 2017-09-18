{-# LANGUAGE DataKinds
           , FlexibleContexts #-}

import Data.Expression
import Data.List hiding (and)
import Data.Maybe
import Data.Singletons
import Ic3
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
-- 0: while (d < h - 1) -- outerloop
--      p := d
--      b := a[d]
--      f := b
--      i := d + 1
-- 1:   while (i < h)   -- innerloop
--        x := a[i]
-- 2:     if (x < b)    -- new minimum
--          b := x
--          p := i
--        i := i + 1
-- 3:   a[d] := b       -- swap
-- 4:   a[p] := f
--      d := d + 1
--
-- assert:
--   forall k l. k < l => a[k] <= a[l] -- sortedness
--
selvs = [ pc, d, h, p, b, f, i, x, k1, k2, ak1, ak2 ]
seli  = pc .=. 0 .&. h .>=. 2 .&. d .=. 0 .&. 0 .<=. k1 .&. k1 .<. k2 .&. k2 .<. h
selp  = pc .=. 5 .->. ak1 .<=. ak2
selt  = k1 .<. k2 .&. (
        -- outer (walk over entire array (prefix is sorted))
        frame selvs ( pc .=. 0 .&. pc' .=. 5 .&. d .>=. h .+. (-1) ) .|.
        frame selvs ( pc .=. 0 .&. pc' .=. 1 .&. d .<.  h .+. (-1) .&. p' .=. d .&. ( d ./=. k1 .&. d ./=. k2 {- .&. b' .=. select a d -} .|. d .=. k1 .&. b' .=. ak1 .|. d .=. k2 .&. b' .=. ak2 ) .&. f' .=. b' .&. i' .=. d .+. 1 ) .|.

        -- inner (find minimum in remainder to be swapped with leftmost element)
        frame selvs ( pc .=. 1 .&. pc' .=. 3 .&. i .>=. h ) .|.
        frame selvs ( pc .=. 1 .&. pc' .=. 2 .&. i .<.  h .&. (i ./=. k1 .&. i ./=. k2 {- .&. x' .=. select a i -} .|. i .=. k1 .&. x' .=. ak1 .|. i .=. k2 .&. x' .=. ak2) ) .|.

        -- if (found new minimum, remember value, and index)
        frame selvs ( pc .=. 2 .&. pc' .=. 1 .&. x .>=. b .&. i' .=. i .+. 1 ) .|.
        frame selvs ( pc .=. 2 .&. pc' .=. 1 .&. x .<.  b .&. b' .=. x .&. p' .=. i .&. i' .=. i .+. 1 ) .|.

        -- swap minimum with leftmost
        frame selvs ( pc .=. 3 .&. pc' .=. 4 .&. ( d ./=. k1 .&. d ./=. k2 {- .&. a' .=. store a d b -} .&. ak1' .=. ak1 .&. ak2' .=. ak2 .|. d .=. k1 .&. ak1' .=. b .&. ak2' .=. ak2 .|. d .=. k2 .&. ak1' .=. ak1 .&. ak2' .=. b ) ) .|.
        frame selvs ( pc .=. 4 .&. pc' .=. 0 .&. ( p ./=. k1 .&. p ./=. k2 {- .&. a' .=. store a p f -} .&. ak1' .=. ak1 .&. ak2' .=. ak2 .|. p .=. k1 .&. ak1' .=. f .&. ak2' .=. ak2 .|. p .=. k2 .&. ak1' .=. ak1 .&. ak2' .=. f ) .&. d' .=. d .+. 1 ) .|.

        -- end
        frame selvs ( pc .=. 5 )
    )

-- Bubble sort
--
-- 0: while (1 < h)
--      i := 0
-- 1:   while (i < h - 1)
--        x := a[i]
--        y := a[i+1]
-- 2:     if (x > y)
--          a[i]   := y
-- 3:       a[i+1] := x
--        i := i + 1
--      h := h - 1
--
--  assert:
--    forall k l. k < l => a[k] <= a[l]
--
bubvs = [ pc, h, i, x, y, k1, k2, ak1, ak2 ]
bubi  = pc .=. 0 .&. h .>=. 2 .&. 0 .<=. k1 .&. k1 .<. k2 .&. k2 .<. h
bubp  = pc .=. 4 .->. ak1 .<=. ak2
bubt  = k1 .<. k2 .&. (
        frame bubvs ( pc .=. 0 .&. pc' .=. 4 .&. 1 .>=. h {- .&. a' .=. a -} ) .|.
        frame bubvs ( pc .=. 0 .&. pc' .=. 1 .&. 1 .<.  h .&. i' .=. 0 {- .&. a' .=. a -} ) .|.

        frame bubvs ( pc .=. 1 .&. pc' .=. 0 .&. i .>=. h .+. (-1) .&. h' .=. h .+. (-1) {- .&. a' .=. a -} ) .|.
        frame bubvs ( pc .=. 1 .&. pc' .=. 2 .&. i .<.  h .+. (-1) .&. ( i ./=. k1 .&. i ./=. k2 {- .&. x' .=. select a i -} .|. i .=. k1 .&. x' .=. ak1 .|. i .=. k2 .&. x' .=. ak2 )
                                                                   .&. ( i .+. 1 ./=. k1 .&. i .+. 1 ./=. k2 {- .&. y' .=. select a (i .+. 1) -} .|. i .+. 1 .=. k1 .&. y' .=. ak1 .|. i .+. 1 .=. k2 .&. y' .=. ak2 )
                                                                   {- .&. a' .=. a -} ) .|.

        frame bubvs ( pc .=. 2 .&. pc' .=. 1 .&. x .<=. y .&. i' .=. i .+. 1 {- .&. a' .=. a -} ) .|.
        frame bubvs ( pc .=. 2 .&. pc' .=. 3 .&. x .>.  y .&. ( i ./=. k1 .&. i ./=. k2 .&. ak1' .=. ak1 .&. ak2' .=. ak2 {- .&. a' .=. store a i y -} .|. i .=. k1 .&. ak1' .=. y .&. ak2' .=. ak2 {- .&. a' .=. a -} .|. i .=. k2 .&. ak1' .=. ak1 .&. ak2' .=. y {- .&. a' .=. a -} ) ) .|.

        frame bubvs ( pc .=. 3 .&. pc' .=. 1 .&. ( i .+. 1 ./=. k1 .&. i .+. 1 ./=. k2 .&. ak1' .=. ak1 .&. ak2' .=. ak2 {- .&. a' .=. store a (i .+. 1) x -} .|. i .+. 1 .=. k1 .&. ak1' .=. x .&. ak2' .=. ak2 {- .&. a' .=. a -} .&. i .+. 1 .=. k2 .&. ak1' .=. ak1 .&. ak2' .=. x {- .&. a' .=. a -} ) .&. i' .=. i .+. 1 ) .|.

        frame bubvs ( pc .=. 4 {- .&. a' .=. a -} )
    )

main = runSolver defaultLog ( ic3 (map (DynamicallySorted sing) bubvs {- ++ [DynamicallySorted sing a] -}) bubi bubt bubp)
