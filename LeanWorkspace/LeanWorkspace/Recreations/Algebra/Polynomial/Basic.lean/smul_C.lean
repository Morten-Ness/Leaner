import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem smul_C {S} [SMulZeroClass S R] (s : S) (r : R) : s • Polynomial.C r = Polynomial.C (s • r) := Polynomial.smul_monomial _ _ r

