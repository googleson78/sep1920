{-# OPTIONS --no-unicode #-}

module Lib.Maybe where

open import Lib.Zero
open import Lib.One
open import Lib.Equality
open import Lib.PartialOrder

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
<M=-trans : {X : Set} {x y z : Maybe X}
         -> x <M= y -> y <M= z
         -> x <M= z
<M=-trans {X} {no} {y} {z} x<=y y<=z = <>
<M=-trans {X} {yes x} {yes .x} {yes .x} refl refl = refl

-- and antisymmetric
<M=-antisym : {X : Set} {x y : Maybe X} -> x <M= y -> y <M= x -> x == y
<M=-antisym {X} {no} {no} p q = refl
<M=-antisym {X} {yes x} {yes .x} refl refl = refl

-- and so it induces a partial order for any set
module MaybeOrder (X : Set) where
  open PartialOrder

  MaybeOrder : PartialOrder
  MaybeOrder = record
    { Obj = Maybe X
    ; _<=_ = _<M=_
    ; <=-refl = <M=-refl
    ; <=-trans = <M=-trans
    ; <=-antisym = <M=-antisym
    }

open MaybeOrder


-- therefore partial functions X -o> X are also a partial ordering for any type X
-- using the induced ordering from -> and Maybe (MaybeOrder) combined
module EndoPartial (X : Set) where
  open PartialOrder

  _<o=_ : (f g : X -o> X) -> Set
  f <o= g = (x : X) -> f x <M= g x

  EndoPartial : PartialOrder
  EndoPartial = record
    { Obj = X -o> X
    ; _<=_ = _<o=_
    ; <=-refl = \ n -> <M=-refl
    ; <=-trans = \ {f} {g} {h} f<=g g<=h x -> -><M=-trans {X} {f} {g} {h} x (f<=g x) (g<=h x)
    ; <=-antisym = \ f<=g g<=h -> ext \ x -> <M=-antisym (f<=g x) (g<=h x)
    }
    where
    -><M=-trans : {X : Set} {f g h : X -o> X} (x : X)
               -> (f x <M= g x) -> (g x <M= h x)
               -> f x <M= h x
    -><M=-trans {X} {f} {g} {h} n f<=g g<=h with f n
    -><M=-trans {X} {f} {g} {h} n f<=g g<=h | no = <>
    -><M=-trans {X} {f} {g} {h} n f<=g g<=h | yes x with g n
    -><M=-trans {X} {f} {g} {h} n f<=g g<=h | yes x | yes y with h n
    -><M=-trans {X} {f} {g} {h} n f<=g g<=h | yes x | yes y | yes z = ==-trans f<=g g<=h

-- these should be functors
-- for now they are nothing
module MonotoneThing where
  open PartialOrder

  record MonotoneThing
    {D : PartialOrder}
    {E : PartialOrder}
    (F : Obj D -> Obj E) : Set
    where
    field
      preserves : {x x' : Obj D} -> _<=_ D x x' -> _<=_ E (F x) (F x')
