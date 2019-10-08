module Lib.Equality where

-- a thing is equal to another thing only if they are exactly one and the same
data _==_ {X : Set} (x : X) : X -> Set where
  refl : x == x

-- allow for "rewrite construct"
{-# BUILTIN EQUALITY _==_ #-}

infix 20 _==_

-- some == lifting utils
_=$=_ : {X Y : Set} {f g : X -> Y}{x y : X} -> f == g -> x == y -> f x == g y
refl =$= refl = refl

_$=_ : {X Y : Set} {x y : X} (f : X -> Y) -> x == y -> f x == f y
f $= x = refl =$= x

_=$ : {X Y : Set} {f g : X -> Y}{x : X} -> f == g -> f x == g x
f =$ = f =$= refl

-- well I actually lied about things being equal only when they are exactly the same
-- two functions are equal if they are pointwise equal
postulate
  ext : {X Y : Set} {f g : X -> Y} -> ((x : X) -> f x == g x) -> f == g

==-trans : {X : Set} {x y z : X} -> x == y -> y == z -> x == z
==-trans refl refl = refl

==-sym : {X : Set} {x y : X} -> x == y -> y == x
==-sym refl = refl

