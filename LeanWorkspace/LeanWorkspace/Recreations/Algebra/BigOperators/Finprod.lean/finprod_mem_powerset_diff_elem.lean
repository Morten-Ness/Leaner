import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_powerset_diff_elem {f : Set α → M} {s : Set α} {a : α} (hs : s.Finite)
    (has : a ∈ s) : ∏ᶠ t ∈ 𝒫 s, f t = (∏ᶠ t ∈ 𝒫 (s \ {a}), f t)
    * ∏ᶠ t ∈ 𝒫 (s \ {a}), f (insert a t) := by
  nth_rw 1 2 [← Set.insert_diff_self_of_mem has] -- second appearance hidden by notation
  exact finprod_mem_powerset_insert (hs.subset Set.diff_subset)
    (notMem_diff_of_mem (Set.mem_singleton a))

