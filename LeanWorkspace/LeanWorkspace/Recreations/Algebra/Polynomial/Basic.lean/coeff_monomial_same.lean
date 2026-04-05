import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_monomial_same (n : ℕ) (c : R) : (Polynomial.monomial n c).coeff n = c := Finsupp.single_eq_same

