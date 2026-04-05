import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_monomial_of_ne {m n : ℕ} (c : R) (h : m ≠ n) : (Polynomial.monomial n c).coeff m = 0 := Finsupp.single_eq_of_ne h

