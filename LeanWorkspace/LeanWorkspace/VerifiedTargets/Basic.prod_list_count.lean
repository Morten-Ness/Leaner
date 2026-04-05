import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_list_count [DecidableEq M] (s : List M) :
    s.prod = ∏ m ∈ s.toFinset, m ^ s.count m := by simpa using Finset.prod_list_map_count s id

