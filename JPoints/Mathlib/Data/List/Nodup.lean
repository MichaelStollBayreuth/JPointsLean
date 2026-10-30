/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.List.Nodup

/-!
# A `flatMap` without duplicates

A candidate for `Mathlib.Data.List.Nodup`: a `flatMap` over a list without duplicates has none
when no piece has any and a function recovers from each element of a piece its index
(`List.Nodup.flatMap`), the form of `List.nodup_flatMap` in which the pieces are disjoint because
their elements carry their index.
-/

@[expose] public section

namespace List

/-- A `flatMap` over a list without duplicates has none when no piece has any and `g` recovers
from each element of a piece its index. -/
theorem Nodup.flatMap {α β : Type*} {l : List α} {f : α → List β} (g : β → α) (hl : l.Nodup)
    (hf : ∀ x ∈ l, (f x).Nodup) (hg : ∀ x ∈ l, ∀ y ∈ f x, g y = x) :
    (l.flatMap f).Nodup :=
  nodup_flatMap.2 ⟨hf, hl.pairwise_of_forall_ne fun x hx x' hx' hne y hy hy' ↦
    hne <| (hg x hx y hy).symm.trans (hg x' hx' y hy')⟩

end List

end
