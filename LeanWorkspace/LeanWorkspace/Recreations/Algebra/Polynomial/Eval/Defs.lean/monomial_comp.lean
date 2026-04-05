import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem monomial_comp (n : ℕ) : (monomial n a).comp p = Polynomial.C a * p ^ n := Polynomial.eval₂_monomial _ _

