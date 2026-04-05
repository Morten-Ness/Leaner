import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natCast_mul_comp {n : ℕ} : ((n : R[X]) * p).comp r = n * p.comp r := by
  rw [← C_eq_natCast, Polynomial.C_mul_comp]

