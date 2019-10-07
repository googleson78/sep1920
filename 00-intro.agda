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

data _<=_ : Nat -> Nat -> Set where
  oz : 0 <= 0
  os : {n m : Nat} -> n <= m -> suc n <= suc m
  o' : {n m : Nat} -> n <= m -> n <= suc m

data _+_ (X Y : Set) : Set where
  inl : X -> X + Y
  inr : Y -> X + Y

Maybe : Set -> Set
Maybe X = One + X

or : {n : Nat} -> n <= n
or {zero} = oz
or {suc n} = os or

th-trans : {n m k : Nat} -> n <= m -> m <= k -> n <= k
th-trans oz m<=k = m<=k
th-trans (os n<=m) (os m<=k) = os (th-trans n<=m m<=k)
th-trans (os n<=m) (o' m<=k) = os (th-trans (o' n<=m) m<=k)
th-trans (o' n<=m) (os m<=k) = o' (th-trans n<=m m<=k)
th-trans (o' n<=m) (o' m<=k) = o' (th-trans (o' n<=m) m<=k)

<=-suc-swap-impossible : {n m : Nat} -> n <= m -> suc m <= n -> Zero
<=-suc-swap-impossible th0 (os th1) = <=-suc-swap-impossible th1 th0
<=-suc-swap-impossible th0 (o' th1) = <=-suc-swap-impossible (th-trans (o' or) th0) th1

<=-suc-refl-impossible : {n : Nat} -> suc n <= n -> Zero
<=-suc-refl-impossible n<=sucn = <=-suc-swap-impossible or n<=sucn

record PartialOrd (X : Set) (_<=_ : X -> X -> Set) : Set where
  field
    <=-refl : {x : X} -> x <= x
    <=-trans : {x y z : X} -> x <= y -> y <= z -> x <= z
    <=-antisym : {x y : X} -> x <= y -> y <= x -> x == y

Nats<=PartialOrd : PartialOrd Nat _<=_
Nats<=PartialOrd =
  record
    { <=-refl = or
    ; <=-trans = th-trans
    ; <=-antisym = help-antisym
    }
    where
    help-antisym : {n m : Nat} -> n <= m -> m <= n -> n == m
    help-antisym oz oz = refl
    help-antisym (os n<=m) (os m<=n) = suc $= help-antisym n<=m m<=n
    help-antisym (os n<=m) (o' m<=n) = naughte (<=-suc-swap-impossible n<=m m<=n)
    help-antisym (o' n<=m) (os m<=n) = naughte (<=-suc-swap-impossible m<=n n<=m)
    help-antisym (o' n<=m) (o' m<=n) = naughte (<=-suc-refl-impossible (th-trans (o' n<=m) m<=n))




-- need to define partial functions !!!
-- functions Nat -> Nat are PO
--NatFuncsPartialOrd : PartialOrd (Nat -> Maybe Nat) λ f g → (n : Nat) -> (f n == no) + Sg Nat \ m -> (f n == yes m) * (g n == yes m)
--NatFuncsPartialOrd = {!!}




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
