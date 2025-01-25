module W.Internal.Indexed where

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Product using (_×_) renaming (proj₁ to fst; proj₂ to snd)

infixr 0 _-:>_

_-:>_ :
    {li : Level} ->
    {i : Set li} ->
    {lp : Level} ->
    (p : i -> Set lp) ->
    {lq : Level} ->
    (q : i -> Set lq) ->
    (x : i) ->
    Set (lp ⊔ lq)
_-:>_ p q x = p x -> q x

record _:*_
    {li : Level}
    {i : Set li}
    {lp : Level}
    (p : i -> Set lp)
    {lq : Level}
    (q : i -> Set lq)
    (x : i) :
        Set (lp ⊔ lq) where
  constructor _,_
  field
    fst : p x
    snd : q x
open _:*_ public

record K
    {li : Level}
    {i : Set li}
    {lp : Level}
    (p : Set lp)
    (x : i) :
        Set lp where
    field
        unK : p
open K public

All :
    {li : Level} ->
    {i : Set li} ->
    {lp : Level} ->
    (p : i -> Set lp) ->
    Set _
All {li} {i} {lp} p = {x : i} -> p x

record Any
    {li : Level}
    {i : Set li}
    {lp : Level}
    (p : i -> Set lp) :
        Set (li ⊔ lp) where
  field
    {x} : i
    unAny : p x
open Any public
