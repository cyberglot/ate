module W.Internal.Timed.Monad where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import W.Internal.Indexed
open import W.Internal.Timed
open import W.Internal.Time

record TimedMonad
  {lp : Level}
  (p : Time -> Time -> Set lp)
  {li : Level}
  {lo : Level}
  (m : (Time -> Set li) -> Time -> Set lo) :
  Set (lp ⊔ lsuc li ⊔ lo) where
  field
    return :
      {v : Time -> Set li} ->
      All (v -:> m v)
    _>>=_ :
      {v : Time -> Set li} ->
      {{iTimedV : Timed p v}} ->
      {w : Time -> Set li} ->
      {{iTimedW : Timed p w}} ->
      ∀ {s} ->
      m v s ->
      (∀ {t} -> Star p s t -> Kripke p v t -> m w t) ->
      m w s
open TimedMonad public
