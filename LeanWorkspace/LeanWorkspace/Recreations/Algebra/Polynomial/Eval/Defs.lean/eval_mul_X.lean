import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem eval_mul_X : (p * Polynomial.X).eval x = p.eval x * x := Polynomial.eval₂_mul_X ..

