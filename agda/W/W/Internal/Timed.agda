module W.Internal.Timed where

open import Level using (Level; _⊔_)
open import W.Internal.Indexed
open import W.Internal.Time

data Star
  {lp : Level}
  (p : Time -> Time -> Set lp)
  (r : Time) :
  (t : Time) -> Set lp where
  Now : Star p r r
  Seq : {s t : Time} -> Star p r s -> p s t -> Star p r t

seq :
  {lp : Level}
  {p : Time -> Time -> Set lp} ->
  {r s t : Time} ->
  Star p r s ->
  Star p s t ->
  Star p r t
seq prs  Now          = prs
seq prs (Seq pst ptu) = Seq (seq prs pst) ptu

record Timed
  {lp : Level}
  (p : Time -> Time -> Set lp)
  {lv : Level}
  (v : Time -> Set lv) :
    Set (lp ⊔ lv) where
  field
    update : ∀ {s t} -> Star p s t -> v s -> v t
open Timed {{...}} public

Kripke :
  {lp : Level}
  (p : Time -> Time -> Set lp)
  {lv : Level}
  (v : Time -> Set lv)
  (s : Time) ->
  Set _
Kripke p v s = {t : Time} -> Star p s t -> v t

kripke :
  {lp : Level}
  {p : Time -> Time -> Set lp}
  {lv : Level}
  {v : Time -> Set lv}
  {{ iTimedV : Timed p v }} ->
  All (v -:> Kripke p v)
kripke v pst = update pst v
