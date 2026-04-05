import Mathlib

variable {ι M M₀ R : Type*}

variable [CommMonoidWithZero M₀] {s : Multiset M₀}

theorem prod_eq_zero (h : (0 : M₀) ∈ s) : s.prod = 0 := by
  rcases Multiset.exists_cons_of_mem h with ⟨s', hs'⟩; simp [hs', Multiset.prod_cons]

