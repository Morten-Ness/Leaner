import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem eval_natCast_mul {n : ℕ} : ((n : R[X]) * p).eval x = n * p.eval x := by
  rw [← C_eq_natCast, Polynomial.eval_C_mul]

