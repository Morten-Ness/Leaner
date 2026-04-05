import Mathlib

theorem prod_Icc_eq_prod_Ico_mul {α : Type*} [CommMonoid α] (f : ℤ → α) {l u : ℤ}
    (h : l ≤ u) : ∏ m ∈ Icc l u, f m = (∏ m ∈ Ico l u, f m) * f u := by
  simp [Icc_eq_cons_Ico h, mul_comm]

