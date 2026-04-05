import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_multiset_count [DecidableEq M] (s : Multiset M) :
    s.prod = ∏ m ∈ s.toFinset, m ^ s.count m := by
  convert Finset.prod_multiset_map_count s id
  rw [Multiset.map_id]

