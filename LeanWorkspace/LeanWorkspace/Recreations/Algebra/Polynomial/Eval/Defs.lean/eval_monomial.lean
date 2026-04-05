import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem eval_monomial {n a} : (monomial n a).eval x = a * x ^ n := Polynomial.eval₂_monomial _ _

