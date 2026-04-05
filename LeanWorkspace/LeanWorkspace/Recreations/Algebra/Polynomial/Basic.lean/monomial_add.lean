import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem monomial_add (n : ℕ) (r s : R) : Polynomial.monomial n (r + s) = Polynomial.monomial n r + Polynomial.monomial n s := (Polynomial.monomial n).map_add _ _

