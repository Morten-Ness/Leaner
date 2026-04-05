import Mathlib

variable {R : Type*}

variable [Semiring R] {p q : SkewPolynomial R}

variable {S S₁ S₂ : Type*}

theorem monomial_def (n : ℕ) (a : R) : SkewPolynomial.monomial n a = single (ofAdd n) a := rfl

