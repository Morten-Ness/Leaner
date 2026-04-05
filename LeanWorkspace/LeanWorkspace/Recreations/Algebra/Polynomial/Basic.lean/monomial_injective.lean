import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem monomial_injective (n : ℕ) : Function.Injective (Polynomial.monomial n : R → R[X]) := (Polynomial.toFinsuppIso R).symm.injective.comp (single_injective n)

