module W.Internal.Time where

data Time : Set where
  Tick : Time -> Time
