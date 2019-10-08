{-# OPTIONS --no-unicode #-}

module 00-intro where

open import Lib.Zero
open import Lib.One
open import Lib.Equality
open import Lib.Sigma
open import Lib.Naturals
open import Lib.Maybe
open import Lib.PartialOrder

-- a sequence is a mapping from natural numbers to a thing
Sequence : (X : Set) -> Set
Sequence X = Nat -> X

-- for P to be true it just needs to be true at every index
AllSeq : {X : Set} (P : X -> Set) -> Sequence X -> Set
AllSeq P seq = (n : Nat) -> P (seq n)

-- a chain is an increasing sequence
module Chain (ord : PartialOrder) where
  open PartialOrder ord

  record Chain : Set where
    constructor _o><o_
    field
      seq : Sequence Obj
      increasing : (n : Nat) -> seq n <= seq (suc n)

open Chain

_isBoundedBy_ : {ord : PartialOrder} -> Chain ord -> PartialOrder.Obj ord -> Set
_isBoundedBy_ {ord} (seq o><o _) x = AllSeq (\y -> y <= x) seq
  where
  open PartialOrder ord

-- least upper bound
-- some thing that is bigger than an entire chain
-- and is also smaller than all other things that are bigger than the entire chain
U_==_ : {ord : PartialOrder} -> Chain ord -> PartialOrder.Obj ord -> Set
U_==_ {ord} chain lub
  = (chain isBoundedBy lub)
  * ((other : Obj) -> chain isBoundedBy other -> lub <= other)
  where
  open PartialOrder ord

-- a Scott domain is a partial ordering in which all chains have a LUB
-- and there exists a "least" element
module SCOTTDOMAIN where
  open PartialOrder

  record ScottDomain : Set1 where
    field
      ord : PartialOrder
      bot : Obj ord
      lub : Chain ord -> Obj ord
      bot-smallest : (x : Obj ord) -> _<=_ ord bot x
      lub-is-LUB : (chain : Chain ord) -> U chain == lub chain

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
    lub-for-functions-is-lub : (chain : Chain EndoPartial) -> U chain == lub-for-functions chain

  EndoScott : ScottDomain
  EndoScott = record
    { ord = EndoPartial
    ; bot = \ x -> no
    ; lub = lub-for-functions
    ; bot-smallest = \ f x -> <>
    ; lub-is-LUB = lub-for-functions-is-lub
    }

PointwiseOrd : PartialOrder -> PartialOrder -> PartialOrder
PointwiseOrd X Y = record
  { Obj = Obj X * Obj Y
  ; _<=_ = \{ (x1 , y1) (x2 , y2) -> (x1 <X= x2) * (y1 <Y= y2) }
  ; <=-refl = <=-refl X ,  <=-refl Y
  ; <=-trans = \{ (fstx<=fsty , sndx<=sndy) (fsty<=fstz , sndy<=sndz) -> <=-trans X fstx<=fsty fsty<=fstz , <=-trans Y sndx<=sndy sndy<=sndz}
  ; <=-antisym = \{ (fstx<=fsty , sndx<=sndy) (fsty<=fstx , sndy<=sndx) -> *-elemwise (<=-antisym X fstx<=fsty fsty<=fstx) (<=-antisym Y sndx<=sndy sndy<=sndx)}
  }
  where
  open PartialOrder
  open PartialOrder X using () renaming (_<=_ to _<X=_)
  open PartialOrder Y using () renaming (_<=_ to _<Y=_)

-- TODO: pointwise products are scott domains
