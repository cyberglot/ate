module W.Internal.Timed.Monad.Free where

open import Level using (Level; _⊔_)
open import W.Internal.Common
open import W.Internal.Indexed
open import W.Internal.Time
open import W.Internal.Timed
open import W.Internal.Timed.Monad

data Free
  (p : Time -> Time -> Set)
  (c : (Time -> Set) -> Time -> Set)
  (v : Time -> Set)
  (s : Time)
  : Set₁ where
  Pure :
    v s ->
    Free p c v s
  Call :
    {w : Time -> Set} ->
    c w s ->
    ({t : Time} -> Star p s t -> w t -> Free p c v t) ->
    Free p c v s

treturn :
  {p : Time -> Time -> Set}
  {c : (Time -> Set) -> Time -> Set}
  {v : Time -> Set}
  {s : Time} ->
  v s ->
  Free p c v s
treturn = Pure

tbind :
  {p : Time -> Time -> Set}
  {c : (Time -> Set) -> Time -> Set}
  {v : Time -> Set} ->
  {{iTimedV : Timed p v}} ->
  {w : Time -> Set} ->
  {{iTimedW : Timed p w}} ->
  {s : Time} ->
  Free p c v s ->
  ({t : Time} -> Star p s t -> Kripke p v t -> Free p c w t) ->
  Free p c w s
tbind (Pure v)   k =
  k Now (kripke v)
tbind (Call c j) k =
  Call c λ psr wr →
    tbind (j psr wr) λ prt kpvt →
      k (seq psr prt) kpvt

instance
  iTimedFree :
    {p : Time -> Time -> Set} ->
    {c : (Time -> Set) -> Time -> Set} ->
    {{iTimedC : Forall (Compose (Timed p) c)}} ->
    {v : Time -> Set} ->
    {{iTimedV : Timed p v}} ->
    Timed p (Free p c v)
  iTimedFree {p} {c} {{superc}} {v} {{superv}} =
    record { update = go }
    where
      go : {s t : Time} → Star p s t → Free p c v s → Free p c v t
      go pst (Pure v)   = Pure (update pst v)
      go psr (Call c k) = Call (update psr c) \ prt -> k (seq psr prt)

instance
  iTimedMonadFree :
    {p : Time -> Time -> Set} ->
    {c : (Time -> Set) -> Time -> Set} ->
    TimedMonad p (Free p c)
  iTimedMonadFree {p} {c} = record
    { return = treturn
    ; _>>=_  = tbind
    }
