import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Ring R] {p q r : R[X]}

theorem eval_intCast {n : ℤ} {x : R} : (n : R[X]).eval x = n := by
  simp only [← Polynomial.C_eq_intCast, Polynomial.eval_C]

