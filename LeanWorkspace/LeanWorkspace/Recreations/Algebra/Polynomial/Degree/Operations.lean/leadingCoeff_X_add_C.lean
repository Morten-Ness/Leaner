import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R]

theorem leadingCoeff_X_add_C [Semiring S] (r : S) : (Polynomial.X + Polynomial.C r).leadingCoeff = 1 := by
  rw [← pow_one (Polynomial.X : S[X]), Polynomial.leadingCoeff_X_pow_add_C zero_lt_one]

