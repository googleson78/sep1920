{-# OPTIONS --no-unicode #-}

module 00-intro where

open import Lib.Zero
open import Lib.One
open import Lib.Equality
open import Lib.Sigma
open import Lib.Naturals

data _+_ (X Y : Set) : Set where
  inl : X -> X + Y
  inr : Y -> X + Y

infixr 30 _+_

-- add a bottom element to any type
data Maybe (X : Set) : Set where
  no : Maybe X
  yes : X -> Maybe X

-- things that are partial orders
-- technically we should probably require that the _<=_
-- operation return types with only one inhabitant
-- but it's not an issue for now (?)
-- we are probably going to need totality at some point though
record PartialOrd : Set1 where
  field
    Obj : Set
    _<=_ : Obj -> Obj -> Set
    <=-refl : {x : Obj} -> x <= x
    <=-trans : {x y z : Obj} -> x <= y -> y <= z -> x <= z
    <=-antisym : {x y : Obj} -> x <= y -> y <= x -> x == y

Nats<N=PartialOrd : PartialOrd
Nats<N=PartialOrd =
  record
    { Obj = Nat
    ; _<=_ = _<N=_
    ; <=-refl = or
    ; <=-trans = <N=-trans
    ; <=-antisym = <N=-antisym
    }

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

-- and so partial functions X -o> X are a partial ordering for any type X
-- using the induced ordering from -> and Maybe combined
-- the ordering induced by X -> Y is simply transferring x's over to Y and comparing them there
module EndoPartial (X : Set) where
  open PartialOrd

  _<o=_ : (f g : X -o> X) -> Set
  f <o= g = (x : X) -> f x <M= g x

  EndoPartial : PartialOrd
  EndoPartial = record
    { Obj = X -o> X
    ; _<=_ = _<o=_
    ; <=-refl = \ n -> <M=-refl
    ; <=-trans = \ {f} {g} {h} f<=g g<=h x -> <M=-trans {X} {f} {g} {h} x (f<=g x) (g<=h x)
    ; <=-antisym = \ f<=g g<=h -> ext \ x -> <M=-antisym (f<=g x) (g<=h x)
    }

-- these should be functors
-- for now they are nothing
module MonotoneThing where
  open PartialOrd

  record MonotoneThing
    {D : PartialOrd}
    {E : PartialOrd}
    (F : Obj D -> Obj E) : Set
    where
    field
      preserves : {x x' : Obj D} -> _<=_ D x x' -> _<=_ E (F x) (F x')

-- a sequence is a mapping from natural numbers to a thing
Sequence : (X : Set) -> Set
Sequence X = (n : Nat) -> X

-- for P to be true it just needs to be true at every index
AllSeq : {X : Set} (P : X -> Set) -> Sequence X -> Set
AllSeq P seq = (n : Nat) -> P (seq n)

-- a chain is an increasing sequence
Chain : PartialOrd -> Set
Chain ord = Sequence Obj >< \ f -> (n : Nat) -> f n <= f (suc n)
  where open PartialOrd ord

-- least upper bound
-- some thing that is bigger than an entire chain
-- and is also smaller than all other things that are bigger than the entire chain
for_U_==_ : (ord : PartialOrd) -> Chain ord -> PartialOrd.Obj ord -> Set
for ord U (seq , increasing) == x
  = AllSeq (\ y -> y <= x) seq
  * ((other : Obj) -> AllSeq (\ y -> y <= other) seq -> x <= other)
  where
  open PartialOrd ord
  open _><_


-- a Scott domain is a partial ordering in which all chains have a LUB
-- and there exists a "least" element
module SCOTTDOMAIN where
  open PartialOrd

  record ScottDomain : Set1 where
    field
      ord : PartialOrd
      bot : Obj ord
      lub : Chain ord -> Obj ord
      bot-smallest : (x : Obj ord) -> _<=_ ord bot x
      lub-is-LUB : (chain : Chain ord) -> for ord U chain == lub chain

open SCOTTDOMAIN

-- partial endofunctions form a scott domain
-- the bot element is the nowhere defined function
-- and the LUB of a sequence of functions would be their set union
module EndoScott (X : Set) where
  open EndoPartial X

  -- :( don't know how you deal with this
  -- it's genuinely non-constructive
  -- you can't know if you will ever reach a point where your f is defined
  postulate
    lub-for-functions : Chain EndoPartial -> X -o> X
    lub-for-functions-is-lub : (chain : Chain EndoPartial) -> for EndoPartial U chain == lub-for-functions chain

  EndoScott : ScottDomain
  EndoScott = record
    { ord = EndoPartial
    ; bot = \ x -> no
    ; lub = lub-for-functions
    ; bot-smallest = \ f x -> <>
    ; lub-is-LUB = lub-for-functions-is-lub
    }

-- pointwise products are scott domains

*-elemwise
  :  {X Y : Set} {u v : X * Y}
  -> _><_.fst u == _><_.fst v
  -> _><_.snd u == _><_.snd v
  -> u == v
*-elemwise refl refl = refl

PointwiseOrd : PartialOrd -> PartialOrd -> PartialOrd
PointwiseOrd X Y = record
  { Obj = Obj X * Obj Y
  ; _<=_ = \{ (x1 , y1) (x2 , y2) -> (x1 <X= x2) * (y1 <Y= y2) }
  ; <=-refl = <=-refl X ,  <=-refl Y
  ; <=-trans = \{ (fstx<=fsty , sndx<=sndy) (fsty<=fstz , sndy<=sndz) -> <=-trans X fstx<=fsty fsty<=fstz , <=-trans Y sndx<=sndy sndy<=sndz}
  ; <=-antisym = \{ (fstx<=fsty , sndx<=sndy) (fsty<=fstx , sndy<=sndx) -> *-elemwise (<=-antisym X fstx<=fsty fsty<=fstx) (<=-antisym Y sndx<=sndy sndy<=sndx)}
  }
  where
  open PartialOrd
  open PartialOrd X using () renaming (_<=_ to _<X=_)
  open PartialOrd Y using () renaming (_<=_ to _<Y=_)
