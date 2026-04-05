import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Ring R] {p q r : R[X]}

theorem root_X_sub_C : Polynomial.IsRoot (Polynomial.X - Polynomial.C a) b ↔ a = b := by
  rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero, eq_comm]

