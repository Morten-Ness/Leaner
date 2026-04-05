import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R]

theorem leadingCoeff_X_pow_add_C {n : ℕ} (hn : 0 < n) {r : R} :
    (Polynomial.X ^ n + Polynomial.C r).leadingCoeff = 1 := by
  nontriviality R
  rw [leadingCoeff, Polynomial.natDegree_X_pow_add_C, coeff_add, coeff_X_pow_self, coeff_C,
    if_neg (pos_iff_ne_zero.mp hn), add_zero]

