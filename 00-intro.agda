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
-- TODO: how about do a global \n -> instead
-- it's very annoying to work with right now
-- because I have two functions and two n's to handle
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

PointwiseOrder : PartialOrder -> PartialOrder -> PartialOrder
PointwiseOrder X Y = record
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

PointwiseScott : ScottDomain -> ScottDomain -> ScottDomain
PointwiseScott
  X@record
    { ord = ordX
    ; bot = botX
    ; lub = lubX
    ; bot-smallest = bot-smallestX
    ; lub-is-LUB = lub-is-LUBX
    }
  Y@record
    { ord = ordY
    ; bot = botY
    ; lub = lubY
    ; bot-smallest = bot-smallestY
    ; lub-is-LUB = lub-is-LUBY
    }
  = help
  where

  open _><_
  open ScottDomain
  open PartialOrder
  open Chain.Chain
  open PartialOrder ordX using () renaming (_<=_ to _<X=_)
  open PartialOrder ordY using () renaming (_<=_ to _<Y=_)

  chainOnFst : {X Y : PartialOrder} -> Chain (PointwiseOrder X Y) -> Chain X
  chainOnFst (seq o><o increasing) = (\ n -> fst (seq n)) o><o \ n -> fst (increasing n)

  chainOnSnd : {X Y : PartialOrder} -> Chain (PointwiseOrder X Y) -> Chain Y
  chainOnSnd (seq o><o increasing) = (\ n -> snd (seq n)) o><o \ n -> snd (increasing n)

  help : ScottDomain
  ord help = PointwiseOrder ordX ordY
  bot help = botX , botY
  lub help = \chain -> lubX (chainOnFst chain) , lubY (chainOnSnd chain)
  bot-smallest help = \{ (x , y) -> (bot-smallestX x) , (bot-smallestY y)}
  lub-is-LUB help chain
    = (\ n -> fst (lub-is-LUBX chainX) n , fst (lub-is-LUBY chainY) n)
    , \{ (x , y) other-is-ub ->
          snd (lub-is-LUBX chainX) x (\ n -> fst (other-is-ub n))
        , snd (lub-is-LUBY chainY) y (\ n -> snd (other-is-ub n))
       }
    where
    chainX = chainOnFst chain
    chainY = chainOnSnd chain
