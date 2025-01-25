module W.Internal.Name where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)

record Name : Set where
  field
    name : String
    uniq : Nat
open Name public
