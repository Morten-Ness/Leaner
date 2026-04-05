import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem eval_one : (1 : R[X]).eval x = 1 := Polynomial.eval₂_one _ _

