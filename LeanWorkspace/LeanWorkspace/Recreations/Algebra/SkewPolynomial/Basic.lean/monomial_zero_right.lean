import Mathlib

variable {R : Type*}

variable [Semiring R] {p q : SkewPolynomial R}

variable {S S₁ S₂ : Type*}

theorem monomial_zero_right (n : ℕ) : SkewPolynomial.monomial n (0 : R) = 0 := single_zero _

