module Lib.Maybe where

open import Lib.Zero
open import Lib.One
open import Lib.Equality

-- add a bottom element to any type
data Maybe (X : Set) : Set where
  no : Maybe X
  yes : X -> Maybe X

-- functions returning a Maybe are partial
_-o>_ : Set -> Set -> Set
X -o> Y = X -> Maybe Y

-- the induced ordering from Maybe
-- everything is only LTE to itself,
-- except for 'no' which is LTE to everything else
_<M=_ : {X : Set} -> Maybe X -> Maybe X -> Set
no <M= y = One
yes x <M= no = Zero
yes x <M= yes y = x == y

-- this is reflexive
<M=-refl : {X : Set} {x : Maybe X} -> x <M= x
<M=-refl {X} {no} = <>
<M=-refl {X} {yes x} = refl

-- and transitive
<M=-trans : {X : Set} {f g h : X -o> X} (x : X)
         -> (f x <M= g x) -> (g x <M= h x)
         -> f x <M= h x
<M=-trans {X} {f} {g} {h} n f<=g g<=h with f n
<M=-trans {X} {f} {g} {h} n f<=g g<=h | no = <>
<M=-trans {X} {f} {g} {h} n f<=g g<=h | yes x with g n
<M=-trans {X} {f} {g} {h} n f<=g g<=h | yes x | yes y with h n
<M=-trans {X} {f} {g} {h} n f<=g g<=h | yes x | yes y | yes z = ==-trans f<=g g<=h

-- and antisymmetric
<M=-antisym : {X : Set} {x y : Maybe X} -> x <M= y -> y <M= x -> x == y
<M=-antisym {X} {no} {no} p q = refl
<M=-antisym {X} {yes x} {yes .x} refl refl = refl
