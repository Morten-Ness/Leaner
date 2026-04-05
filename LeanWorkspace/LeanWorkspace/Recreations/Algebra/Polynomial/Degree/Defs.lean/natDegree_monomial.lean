import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_monomial [DecidableEq R] (i : ℕ) (r : R) :
    Polynomial.natDegree (monomial i r) = if r = 0 then 0 else i := by
  split_ifs with hr
  · simp [hr]
  · rw [← C_mul_X_pow_eq_monomial, Polynomial.natDegree_C_mul_X_pow i r hr]

