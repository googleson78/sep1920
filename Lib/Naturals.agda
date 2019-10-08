module Lib.Naturals where

open import Lib.Zero
open import Lib.Equality

-- peano naturals
data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

-- allows us to write nat literals
{-# BUILTIN NATURAL Nat #-}

-- LEQ ordering on the natural numbers
-- but also holding additional information on "how"
-- one number is less than another
-- so called "thinnings" - ways to embed one vector thing into another
data _<N=_ : Nat -> Nat -> Set where
  oz : 0 <N= 0
  os : {n m : Nat} -> n <N= m -> suc n <N= suc m
  o' : {n m : Nat} -> n <N= m -> n <N= suc m

or : {n : Nat} -> n <N= n
or {zero} = oz
or {suc n} = os or

<N=-trans : {n m k : Nat} -> n <N= m -> m <N= k -> n <N= k
<N=-trans oz m<N=k = m<N=k
<N=-trans (os n<N=m) (os m<N=k) = os (<N=-trans n<N=m m<N=k)
<N=-trans (os n<N=m) (o' m<N=k) = os (<N=-trans (o' n<N=m) m<N=k)
<N=-trans (o' n<N=m) (os m<N=k) = o' (<N=-trans n<N=m m<N=k)
<N=-trans (o' n<N=m) (o' m<N=k) = o' (<N=-trans (o' n<N=m) m<N=k)

<N=-suc-swap-impossible : {n m : Nat} -> n <N= m -> suc m <N= n -> Zero
<N=-suc-swap-impossible th0 (os th1) = <N=-suc-swap-impossible th1 th0
<N=-suc-swap-impossible th0 (o' th1) = <N=-suc-swap-impossible (<N=-trans (o' or) th0) th1

<N=-suc-refl-impossible : {n : Nat} -> suc n <N= n -> Zero
<N=-suc-refl-impossible n<N=sucn = <N=-suc-swap-impossible or n<N=sucn

<N=-antisym : {n m : Nat} -> n <N= m -> m <N= n -> n == m
<N=-antisym oz oz = refl
<N=-antisym (os n<N=m) (os m<N=n) = suc $= <N=-antisym n<N=m m<N=n
<N=-antisym (os n<N=m) (o' m<N=n) = naughte (<N=-suc-swap-impossible n<N=m m<N=n)
<N=-antisym (o' n<N=m) (os m<N=n) = naughte (<N=-suc-swap-impossible m<N=n n<N=m)
<N=-antisym (o' n<N=m) (o' m<N=n) = naughte (<N=-suc-refl-impossible (<N=-trans (o' n<N=m) m<N=n))
