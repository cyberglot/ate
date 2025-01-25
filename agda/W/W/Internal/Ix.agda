module W.Internal.Ix where

open import Agda.Builtin.Nat using (Nat) renaming (zero to Z; suc to S)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)

data Ix : (n : Nat) -> Set where
  FZ : {n : Nat} -> Ix (S n)
  FS : {n : Nat} -> Ix n -> Ix (S n)

thin : {n : Nat} -> Ix (S n) -> Ix n -> Ix (S n)
thin  FZ        y  = FS y
thin (FS _)  FZ    = FZ
thin (FS x) (FS y) = FS (thin x y)

data Pos : (n : Nat) -> Set where
  MkPos : {n : Nat} -> Pos (S n)

isPos : {n : Nat} -> Ix n -> Pos n
isPos  FZ    = MkPos
isPos (FS _) = MkPos

thick : {n : Nat} -> Ix (S n) -> Ix (S n) -> Maybe (Ix n)
thick  FZ     FZ    = nothing
thick  FZ    (FS j) = just j
thick (FS i)  FZ    = case isPos i of \{ MkPos -> just FZ }
thick (FS i) (FS j) = case isPos i of \{ MkPos -> FS <$> thick i j}
