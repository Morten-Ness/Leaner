import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_powerset_insert {f : Set α → M} {s : Set α} {a : α} (hs : s.Finite)
    (has : a ∉ s) : ∏ᶠ t ∈ 𝒫 insert a s, f t = (∏ᶠ t ∈ 𝒫 s, f t) * ∏ᶠ t ∈ 𝒫 s, f (insert a t) := by
  rw [Set.powerset_insert,
    finprod_mem_union (disjoint_powerset_insert has) hs.powerset (hs.powerset.image (insert a)),
    finprod_mem_image (powerset_insert_injOn has)]

