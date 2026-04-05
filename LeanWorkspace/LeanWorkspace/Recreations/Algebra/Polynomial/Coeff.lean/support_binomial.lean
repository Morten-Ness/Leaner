import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem support_binomial {k m : ℕ} (hkm : k ≠ m) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) :
    support (Polynomial.C x * Polynomial.X ^ k + Polynomial.C y * Polynomial.X ^ m) = {k, m} := by
  apply subset_antisymm (support_binomial' k m x y)
  simp_rw [insert_subset_iff, singleton_subset_iff, mem_support_iff, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_self, mul_one, Polynomial.coeff_X_pow, if_neg hkm, if_neg hkm.symm, mul_zero, zero_add,
    add_zero, Ne, hx, hy, not_false_eq_true, and_true]

