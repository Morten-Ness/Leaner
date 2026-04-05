import Mathlib

theorem prod_Icc_succ_eq_mul_endpoints {R : Type*} [CommGroup R] (f : ℤ → R) {N : ℕ} :
    ∏ m ∈ Icc (-(N + 1) : ℤ) (N + 1), f m =
    f (N + 1) * f (-(N + 1) : ℤ) * ∏ m ∈ Icc (-N : ℤ) N, f m := by
  induction N
  · rw [Icc_succ_succ]
    grind
  · rw [Icc_succ_succ, prod_union (by simp)]
    grind

