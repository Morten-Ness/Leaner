import Mathlib

variable {R : Type*}

variable [Semiring R] {p q : SkewPolynomial R}

variable {S S₁ S₂ : Type*}

theorem monomial_zero_one [MulSemiringAction (Multiplicative ℕ) R] : SkewPolynomial.monomial (0 : ℕ) (1 : R) = 1 := rfl

