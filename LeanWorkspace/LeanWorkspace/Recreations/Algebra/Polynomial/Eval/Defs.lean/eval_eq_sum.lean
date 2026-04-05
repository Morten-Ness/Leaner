import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem eval_eq_sum : p.eval x = p.sum fun e a => a * x ^ e := by
  rw [Polynomial.eval, Polynomial.eval₂_eq_sum]
  rfl

