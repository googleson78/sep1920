{-# OPTIONS --no-unicode #-}

module 00-intro where

data Zero : Set where

naughte : {X : Set} -> Zero -> X
naughte ()

record One : Set where
  constructor <>

data _==_ {X : Set} (x : X) : X -> Set where
  refl : x == x

{-# BUILTIN EQUALITY _==_ #-}

infix 20 _==_

_=$=_ : {X Y : Set} {f g : X -> Y}{x y : X} -> f == g -> x == y -> f x == g y
refl =$= refl = refl

_$=_ : {X Y : Set} {x y : X} (f : X -> Y) -> x == y -> f x == f y
f $= x = refl =$= x

_=$ : {X Y : Set} {f g : X -> Y}{x : X} -> f == g -> f x == g x
f =$ = f =$= refl

postulate
  ext : {X Y : Set} {f g : X -> Y} -> ((x : X) -> f x == g x) -> f == g

==-trans : {X : Set} {x y z : X} -> x == y -> y == z -> x == z
==-trans refl refl = refl

==-sym : {X : Set} {x y : X} -> x == y -> y == x
==-sym refl = refl

record _><_ (X : Set) (P : X -> Set) : Set where
  constructor _,_
  field
    x : X
    px : P x

_*_ : (X Y : Set) -> Set
X * Y = X >< \ _ -> Y

infixr 41 _><_
infixr 40 _*_

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}
data _+_ (X Y : Set) : Set where
  inl : X -> X + Y
  inr : Y -> X + Y

infixr 30 _+_

data Maybe (X : Set) : Set where
  no : Maybe X
  yes : X -> Maybe X

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

record PartialOrd (X : Set) (_<=_ : X -> X -> Set) : Set where
  field
    <=-refl : {x : X} -> x <= x
    <=-trans : {x y z : X} -> x <= y -> y <= z -> x <= z
    <=-antisym : {x y : X} -> x <= y -> y <= x -> x == y

Nats<N=PartialOrd : PartialOrd Nat _<N=_
Nats<N=PartialOrd =
  record
    { <=-refl = or
    ; <=-trans = <N=-trans
    ; <=-antisym = help-antisym
    }
    where
    help-antisym : {n m : Nat} -> n <N= m -> m <N= n -> n == m
    help-antisym oz oz = refl
    help-antisym (os n<N=m) (os m<N=n) = suc $= help-antisym n<N=m m<N=n
    help-antisym (os n<N=m) (o' m<N=n) = naughte (<N=-suc-swap-impossible n<N=m m<N=n)
    help-antisym (o' n<N=m) (os m<N=n) = naughte (<N=-suc-swap-impossible m<N=n n<N=m)
    help-antisym (o' n<N=m) (o' m<N=n) = naughte (<N=-suc-refl-impossible (<N=-trans (o' n<N=m) m<N=n))

_-o>_ : Set -> Set -> Set
X -o> Y = X -> Maybe Y

_<M=_ : {X : Set} -> Maybe X -> Maybe X -> Set
no <M= y = One
yes x <M= no = Zero
yes x <M= yes y = x == y

<M=-refl : {X : Set} {x : Maybe X} -> x <M= x
<M=-refl {X} {no} = <>
<M=-refl {X} {yes x} = refl

<M=-trans : {X : Set} {f g h : X -o> X} (x : X)
         -> (f x <M= g x) -> (g x <M= h x)
         -> f x <M= h x
<M=-trans {X} {f} {g} {h} n f<=g g<=h with f n
<M=-trans {X} {f} {g} {h} n f<=g g<=h | no = <>
<M=-trans {X} {f} {g} {h} n f<=g g<=h | yes x with g n
<M=-trans {X} {f} {g} {h} n f<=g g<=h | yes x | yes y with h n
<M=-trans {X} {f} {g} {h} n f<=g g<=h | yes x | yes y | yes z = ==-trans f<=g g<=h

<M=-antisym : {X : Set} {x y : Maybe X} -> x <M= y -> y <M= x -> x == y
<M=-antisym {X} {no} {no} p q = refl
<M=-antisym {X} {yes x} {yes .x} refl refl = refl

module EndoPartial (X : Set) where
  open PartialOrd

  _<o=_ : (f g : X -o> X) -> Set
  f <o= g = (n : X) -> f n <M= g n

  EndoPartial : PartialOrd (X -o> X) _<o=_
  EndoPartial = record
    { <=-refl = \ n -> <M=-refl
    ; <=-trans = \ {f} {g} {h} f<=g g<=h n -> <M=-trans {X} {f} {g} {h} n (f<=g n) (g<=h n)
    ; <=-antisym = \ f<=g g<=h -> ext \ n -> <M=-antisym (f<=g n) (g<=h n)
    }



-- ?
record MonotoneThing {X Y : Set}
                     {_<X=_ : X -> X -> Set}
                     {_<Y=_ : Y -> Y -> Set}
                     {D : PartialOrd X _<X=_}
                     {E : PartialOrd Y _<Y=_}
                     (F : X -> Y) : Set where
  field
    preserves : {x x' : X} -> x <X= x' -> F x <Y= F x'

-- chains?

-- least upper bounds

-- scott domain
-- all chains have a LUB
-- least element (bottom)

-- (F -> Maybe F) form a Scott domain

-- pointwise products are scott domains
