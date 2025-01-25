module W.Internal.Common where

open import Level using (Level; _⊔_)

-- Only sensible things here

Forall :
  {la : Level} ->
  {lp : Level} ->
  {a : Set la} ->
  (p : a -> Set lp) ->
  Set (la ⊔ lp)
Forall p = ∀ {x} -> p x

Compose :
  {la : Level}
  {lb : Level}
  {lc : Level}
  {a : Set la}
  {b : Set lb}
  {c : Set lc} ->
  (b -> c) ->
  (a -> b) ->
  (a -> c)
Compose f g = \ x -> f (g x)
