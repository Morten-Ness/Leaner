import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem smul_monomial {S} [SMulZeroClass S R] (a : S) (n : ℕ) (b : R) :
    a • Polynomial.monomial n b = Polynomial.monomial n (a • b) := Polynomial.toFinsupp_injective <| AddMonoidAlgebra.smul_single _ _ _

