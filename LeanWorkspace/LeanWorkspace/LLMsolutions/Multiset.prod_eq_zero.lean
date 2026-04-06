import Mathlib

variable {ι M M₀ R : Type*}

variable [CommMonoidWithZero M₀] {s : Multiset M₀}

theorem prod_eq_zero (h : (0 : M₀) ∈ s) : s.prod = 0 := by
  induction s using Multiset.induction_on with
  | empty =>
      cases h
  | @cons a s ih =>
      rw [Multiset.mem_cons] at h
      rw [Multiset.prod_cons]
      rcases h with rfl | h
      · simp
      · rw [ih h, mul_zero]
