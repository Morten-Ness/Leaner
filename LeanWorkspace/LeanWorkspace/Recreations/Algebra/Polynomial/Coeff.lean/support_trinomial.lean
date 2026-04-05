import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem support_trinomial {k m n : ℕ} (hkm : k < m) (hmn : m < n) {x y z : R} (hx : x ≠ 0)
    (hy : y ≠ 0) (hz : z ≠ 0) :
    support (Polynomial.C x * Polynomial.X ^ k + Polynomial.C y * Polynomial.X ^ m + Polynomial.C z * Polynomial.X ^ n) = {k, m, n} := by
  apply subset_antisymm (support_trinomial' k m n x y z)
  simp_rw [insert_subset_iff, singleton_subset_iff, mem_support_iff, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_self, mul_one, Polynomial.coeff_X_pow, if_neg hkm.ne, if_neg hkm.ne', if_neg hmn.ne,
    if_neg hmn.ne', if_neg (hkm.trans hmn).ne, if_neg (hkm.trans hmn).ne', mul_zero, add_zero,
    zero_add, Ne, hx, hy, hz, not_false_eq_true, and_true]

