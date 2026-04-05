import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem monomial_mul_monomial (n m : ℕ) (r s : R) :
    Polynomial.monomial n r * Polynomial.monomial m s = Polynomial.monomial (n + m) (r * s) := Polynomial.toFinsupp_injective <| by
    simp only [Polynomial.toFinsupp_monomial, Polynomial.toFinsupp_mul, AddMonoidAlgebra.single_mul_single]

