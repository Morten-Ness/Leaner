import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem eval_X_pow {x : R} (n : ℕ) : (Polynomial.X ^ n : R[X]).eval x = x ^ n := by
  simp [Polynomial.eval]

