import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem divX_X_pow : Polynomial.divX (Polynomial.X ^ n : R[X]) = if (n = 0) then 0 else Polynomial.X ^ (n - 1) := by
  cases n
  · simp
  · ext n
    simp [coeff_X_pow]

