-- Supplementary materials for the course of logic and relational programming, 2025
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- SLD-resolution.
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module SLD where

import Term 
import Unify
import qualified Data.Map as Map
import qualified Control.Monad as Monad
import qualified Control.Monad.State as St
import Debug.Trace()

-- Predicate names
type Pred = Int

-- Atomic formula
type A = (Pred, [T])

-- A class type to convert data structures to/from
-- atomic formulas
class Atomic a where
  toAtomic   :: a -> A
  fromAtomic :: A -> a 

-- Horn clause
data H = A :- [A] deriving Show

-- Program
type P = [H]

-- Unification for atomic formulas
instance Unifiable A where
  unify Nothing _ _ = Nothing
  unify s (p1, ts1) (p2, ts2) = if p1 /= p2 then Nothing else
                                             let unifyPair s (t1, t2) = unify s t1 t2 in
                                                      foldl unifyPair s (zip ts1 ts2)   
  
-- Substitution application to atomic formulas
instance Substitutable A where
  apply s (p, ts) = (p, map (apply s) ts)

instance Substitutable [A] where
  apply s = map (apply s)

-- State
--   1. A triple
--      1. a tail of a program to match against
--	    2. current goal
--	    3. current substitution
--   2. A stack of triplets as in the previous item
--   3. An index of first fresh variable
type Triplet = (P, [A], Subst)
type State   = (Triplet, [Triplet], Var)

-- Makes an initial state from a program and list of goals
-- 1000 is a hardcoded maximal number of variables in a goal
initState :: P -> [A] -> State
initState p g = ((p, g, empty), [], 1000)

-- Refresh all variables in a term
refresh :: T -> St.State (Var, Map.Map Var Var) T
refresh (V x) = do
  (i, m) <- St.get
  case Map.lookup x m of
    Nothing ->
      do St.put (i+1, Map.insert x i m)
         return (V i)
    Just j -> return (V j)
refresh (C c ts) = Monad.liftM (C c) $ mapM refresh ts

-- Refresh all variables in atomic formula
refreshA :: A -> St.State (Var, Map.Map Var Var) A
refreshA (p, ts) = Monad.liftM (p,) $ mapM refresh ts

-- Refresh all variables in a horn clause
refreshH :: H -> St.State (Var, Map.Map Var Var) H
refreshH (a :- as) = Monad.liftM (\ (a:as) -> (a :- as)) $ mapM refreshA (a:as)

-- Rename a clause
rename :: H -> Var -> (H, Var)
rename h v =
  let (h', (v', _)) = St.runState (refreshH h) (v, Map.empty) in
  (h', v')

-- Top-level evaluator: takes
--   1. a program
--   2. a query
--   3. returns a list of substitutions
eval :: P -> [A] -> [Subst]
eval p g = evalRec p $ initState p g

-- Recursive evalutor
evalRec :: P -> State -> [Subst] 
evalRec _ ((_, [], subst), [], _) = [subst]
evalRec _ (([], _, _), [], _) = []
evalRec p ((_, [], subst), top : st, fresh) = subst : evalRec p (top, st, fresh)
evalRec p (([], _, _), top : st, fresh) = evalRec p (top, st, fresh)
evalRec p ((h : p', g : gs, subst), stack, fresh) = let (head' :- tail', fresh') = rename h fresh in
                                                                      case unify (Just subst) head' g of
                                                                        Just subst' -> case tail' of
                                                                                        [] -> evalRec p ((p, apply subst' gs, subst' <+> subst), (p', g : gs, subst) : stack, fresh')
                                                                                        _ -> evalRec p ((p, apply subst' (tail' ++ gs), subst' <+> subst), (p', g : gs, subst) : stack, fresh')
                                                                        Nothing -> evalRec p ((p', g : gs, subst), stack, fresh')

------------------------------------------
--- Some relations for natural numbers ---
------------------------------------------

--- Some predefined variables
x = V 0
y = V 1
z = V 2
t = V 3
u = V 4
v = V 5

--- Terms
o   = C 0 []
s t = C 1 [t]

--- Predicates
add (x, y, z) = (0, [x, y, z])
mul (x, y, z) = (1, [x, y, z])
lt  (x, y)    = (2, [x, y])
le  (x, y)    = (3, [x, y])

--- Specifications
addPeano = [add (o, x, x) :- [], add (s(x), y, s(z)) :- [add (x, y, z)]]
mulPeano = [mul (o, x, o) :- [], mul (s(x), y, z) :- [add (t, y, z), mul (x, y, t)]]
ltPeano  = [lt (o, s(x)) :- [], lt (s(x), s(y)) :- [lt (x, y)]]
lePeano  = [le (o, x) :- [], le (s(x), s(y)) :- [le (x, y)]]

peano = addPeano ++ mulPeano ++ ltPeano ++ lePeano

fromNat :: Integer -> T
fromNat 0 = o
fromNat n = s (fromNat $ n - 1)

one = s (o)
two = s (s (o))

toNat :: T -> Integer
toNat (C 0 []) = 0
toNat (C 1 [t]) = 1 + toNat t
toNat _ = undefined

showPeano n = show $ toNat n

--- Samples
s0 = case eval peano [add (one, one, x)] of
       []    -> "error: should find a solution"
       h : _ -> "solution: " ++ showPeano (apply h x)

s1 = case eval peano [add (x, one, two)] of
       []    -> "error: should find a solution"
       h : _ -> "solution: " ++ showPeano (apply h x)

s2 = case eval peano [add (x, y, two)] of
       []               -> "error: should find a soultion"
       h1 : h2 : h3 : _ -> "solutions: x = " ++ showPeano (apply h1 x) ++ ", y = " ++ showPeano (apply h1 y) ++ "\n" ++
                           "           x = " ++ showPeano (apply h2 x) ++ ", y = " ++ showPeano (apply h2 y) ++ "\n" ++
                           "           x = " ++ showPeano (apply h3 x) ++ ", y = " ++ showPeano (apply h3 y) ++ "\n"

s3 = case eval peano [mul (two, two, x)] of
       []    -> "error: should find a solution"
       h : _ -> "solution: " ++ showPeano (apply h x)

s4 = case eval peano [mul (x, y, fromNat 6)] of
       h1 : h2 : h3 : h4 : _ -> "solutions: x = " ++ showPeano (apply h1 x) ++ ", y = " ++ showPeano (apply h1 y) ++ "\n" ++
                                "           x = " ++ showPeano (apply h2 x) ++ ", y = " ++ showPeano (apply h2 y) ++ "\n" ++
                                "           x = " ++ showPeano (apply h3 x) ++ ", y = " ++ showPeano (apply h3 y) ++ "\n" ++
                                "           x = " ++ showPeano (apply h4 x) ++ ", y = " ++ showPeano (apply h4 y) ++ "\n"
       _    -> "error: should find a solution"

s5 = case eval peano [mul (x, two, fromNat 5)] of
       []    -> "ok: 2 doesn't divide 5"
       h : _ -> "error: solution: " ++ showPeano (apply h x)

s6 = case eval peano [lt (one, x), lt (one, y), mul (x, y, fromNat 10)] of
       h1 : h2 : _ -> "solutions: x = " ++ showPeano (apply h1 x) ++ ", y = " ++ showPeano (apply h1 y) ++ "\n" ++
                                "           x = " ++ showPeano (apply h2 x) ++ ", y = " ++ showPeano (apply h2 y) ++ "\n"
       _           -> "error: should find a solution"

s7 = case eval peano [le (x, two), lt (one, x)] of
       []    -> "error: should find a solution"
       h : _ -> "solution: " ++ showPeano (apply h x)

nil = C 2 []
cons t l = C 3 [t, l]

append (l, t, u) = (4, [l, t, u])
minElem (x, l) = (5, [x, l])
sorted (l, l') = (6, [l, l'])

listAppend = [append (nil, x, x) :- [], append (cons x y, z, cons x t) :- [append (y, z, t)]]
listMin    = [minElem (x, nil) :- [], minElem (x, cons y z) :- [le (x, y), minElem (x, z)]]
listSort   = [sorted (nil, nil) :- [], sorted (x, cons y z) :- [append (t, cons y u, x),
                                                                append (t, u, v),
                                                                minElem (y, x),
                                                                sorted (v, z)]]
listBuggySort   = [sorted (nil, nil) :- [], sorted (x, cons y z) :- [append (t, cons y u, x),
                                                                append (t, u, v),
                                                                minElem (y, z),
                                                                sorted (v, z)]]

lists = peano ++ listAppend ++ listMin ++ listSort
listsBuggy = peano ++ listAppend ++ listMin ++ listBuggySort

toPList = foldr cons nil

toHList (C 2 []) = []
toHList (C 3 [t, l]) = t : toHList l
toHList _ = undefined

showPList l = show $ map toNat (toHList l)

l0 = case eval lists [append (toPList [one], toPList [two], x)] of
       []    -> "error: should find a solution"
       h : _ -> "solution: " ++ showPList (apply h x)

l1 = case eval lists [append (toPList [one, x], toPList [two], toPList [one, fromNat 10, two])] of
       []    -> "error: should find a solution"
       h : _ -> "solution: " ++ showPeano (apply h x)

l2 = case eval lists [sorted (toPList [fromNat 3, fromNat 1, fromNat 5, fromNat 4], x)] of
       []    -> "error: should find a solution"
       h : _ -> "solution: " ++ showPList (apply h x)

-- Diverges
l2Buggy = case eval listsBuggy [sorted (toPList [fromNat 3, fromNat 1, fromNat 5, fromNat 4], x)] of
       []    -> "error: should find a solution"
       h : _ -> "solution: " ++ showPList (apply h x)

mulBuggy = addPeano ++ [mul (o, x, o) :- [], mul (s(x), y, z) :- [mul (y, x, t), add (t, y, z)]]

-- Diverges, doesn't find any solutions
s4Buggy = case eval mulBuggy [mul (x, y, fromNat 6)] of
       h1 : h2 : h3 : h4 : _ -> "solutions: x = " ++ showPeano (apply h1 x) ++ ", y = " ++ showPeano (apply h1 y) ++ "\n" ++
                                "           x = " ++ showPeano (apply h2 x) ++ ", y = " ++ showPeano (apply h2 y) ++ "\n" ++
                                "           x = " ++ showPeano (apply h3 x) ++ ", y = " ++ showPeano (apply h3 y) ++ "\n" ++
                                "           x = " ++ showPeano (apply h4 x) ++ ", y = " ++ showPeano (apply h4 y) ++ "\n"
       _    -> "error: should find a solution"
