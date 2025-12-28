-- Supplementary materials for the course of logic and relational programming, 2025
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- MicroKanren.
{-# LANGUAGE DeriveFunctor #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module MK where

import Control.Monad
import Control.Applicative
import qualified Term as T
import qualified Unify as U

data Stream a =
  Nil                 |
  Mature a (Stream a) |
  Immature (Stream a) deriving Functor

pick :: Integer -> Stream a -> [a]
pick n s =
  case n of
    0 -> []
    _ -> case s of
           Nil           -> []
           Mature   h tl -> h : pick (n-1) tl
           Immature fs   -> pick n fs  

instance Applicative Stream where
  pure f = Mature f $ pure f 
  (<*>)  = ap

instance Alternative Stream where
  empty   = Nil
  Nil <|> s = s
  Immature s <|> s' = Immature (s' <|> s)
  Mature h tl <|> s' = Mature h $ tl <|> s' 
    
instance Monad Stream where
  Nil >>= _ = Nil
  Immature s >>= f = Immature $ s >>= f
  Mature h tl >>= f = f h <|> (tl >>= f) 

instance MonadPlus Stream where
  mzero = empty
  mplus = (<|>)
  
type State = (T.Subst, Int)
type Goal  = State -> Stream State

infix 4 ===

toStream fresh subst = Mature (subst, fresh) Nil

(===) :: T.T -> T.T -> Goal
t1 === t2 = \(subst, fresh) -> maybe Nil (toStream fresh) (U.unify (Just subst) t1 t2)

infixr 3 &&&

(&&&) :: Goal -> Goal -> Goal
(&&&) = (>=>)

infixr 2 |||

(|||) :: Goal -> Goal -> Goal
g1 ||| g2 = \st -> g1 st <|> g2 st

call_fresh :: (T.T -> Goal) -> Goal
call_fresh f (subst, fresh) = f (T.V fresh) (subst, fresh + 1)

delay :: Goal -> Goal
delay f s = Immature $ f s

--- Initial state & run
initial = (T.empty, 1000)
peep x (s, _) = map (T.apply s) x
run peeper goal = map peeper $ pick (-1) $ goal initial

------------------------------------------
--- Some relations for natural numbers ---
------------------------------------------

--- Some predefined variables
x = T.V 0
y = T.V 1
z = T.V 2

--- Terms
o   = T.C 0 []
s t = T.C 1 [t]

add x y z = delay $
  x === o &&& y === z |||
  call_fresh (\ x' ->
  call_fresh (\ z' ->
    x === s x' &&&
    z === s z' &&&
    add x' y z'
  ))

s0 = run (peep [x])    (add (s o) (s o) x)
s1 = run (peep [x])    (add x (s o) (s (s o)))
s2 = run (peep [x, y]) (add x y (s (s o)))
  
nil = T.C 2 []
cons t l = T.C 3 [t, l]

leo x y = delay $
  x === o |||
  call_fresh (\ x' ->
  call_fresh (\ y' ->
    x === s x' &&&
    y === s y' &&&
    leo x' y'
  ))

appendo l t u = delay $
  l === nil &&& t === u |||
  call_fresh (\ x ->
  call_fresh (\ l' ->
  call_fresh (\ u' ->
    l === cons x l' &&&
    u === cons x u' &&&
    appendo l' t u'
  )))  

mino x l = delay $
  l === nil |||
  call_fresh (\ y ->
  call_fresh (\ l' ->
    l === cons y l' &&&
    leo x y &&&
    mino x l'
  ))

sorto l t = delay $
  l === nil &&& t === nil |||
  call_fresh (\ x ->
  call_fresh (\ t' ->
  call_fresh (\ l' ->
  call_fresh (\ u ->
  call_fresh (\ v ->
    t === cons x t' &&&
    appendo u (cons x v) l &&&
    appendo u v l' &&&
    mino x l' &&& -- like buggy sort from SLD but works
    sorto l' t'
  )))))

fromNat :: Integer -> T.T
fromNat 0 = o
fromNat n = s (fromNat $ n - 1)

toNat :: T.T -> Integer
toNat (T.C 0 []) = 0
toNat (T.C 1 [t]) = 1 + toNat t
toNat _ = undefined

showPeano :: T.T -> String
showPeano n = show $ toNat n

toPList :: [T.T] -> T.T
toPList = foldr cons nil

toHList (T.C 2 []) = []
toHList (T.C 3 [t, l]) = t : toHList l
toHList _ = undefined

showPList l = show $ map toNat (toHList l)

l0 = map showPList $ concat $
      run
        (peep [x])
        (sorto (toPList [fromNat 3, fromNat 1, fromNat 5]) x)

mul x y z = delay $
  x === o &&& z === o |||
  call_fresh (\ t ->
  call_fresh (\ x' ->
    x === s x' &&&
    mul y x' t &&&
    add t y z
  ))

-- Diverges but finds all solutions
s4 = map (map showPeano) $
      run
        (peep [x, y])
        (mul x y (fromNat 10))
