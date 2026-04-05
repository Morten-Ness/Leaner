import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem monomial_add_erase (p : R[X]) (n : ℕ) : Polynomial.monomial n (Polynomial.coeff p n) + p.erase n = p := Polynomial.toFinsupp_injective <| by
    rw [Polynomial.toFinsupp_add, Polynomial.toFinsupp_monomial, Polynomial.toFinsupp_erase, Polynomial.coeff]
    exact Finsupp.single_add_erase _ _

