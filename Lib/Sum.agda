{-# OPTIONS --no-unicode #-}

module Sum where

data _+_ (X Y : Set) : Set where
  inl : X -> X + Y
  inr : Y -> X + Y

infixr 30 _+_
