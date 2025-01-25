module W where

open import Level using (Level)
open import W.Internal.Indexed
open import W.Internal.Ix
open import W.Internal.Name
open import W.Internal.Time

data Ty (n : Nat) : Set where
  E : Name -> Ty n
  U : Ix n -> Ty n
  _:=>_ : Ty n -> Ty n -> Ty n

record TyAt (t : Time) : Set where
  inductive
  field
    unTyAt : Ty Z -> TyAt t
open TyAt public

data Sch (n : Nat) : Set where
  T : Ty n         -> Sch n
  P : Sch (S n) -> Sch n

record SchAt (t : Time) : Set where
  inductive
  field
    unSchAt : Sch Z -> SchAt t
open SchAt public

-- Step
record Sub (s t : Time) : Set where
  field
    targetName : Name
    replacementTy : Ty Z
open Sub public

-- &>
data Subs (r : Time) : (t : Time) -> Set where
  Id   : Subs r r
  _:<_ : {s t : Time} -> Subs r s -> Sub s t -> Subs r t
