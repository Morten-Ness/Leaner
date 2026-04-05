import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_monomial_succ : Polynomial.coeff (Polynomial.monomial (n + 1) a) 0 = 0 := by simp [Polynomial.coeff_monomial]

