import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem C_injective : Function.Injective (Polynomial.C : R → R[X]) := Polynomial.monomial_injective 0

