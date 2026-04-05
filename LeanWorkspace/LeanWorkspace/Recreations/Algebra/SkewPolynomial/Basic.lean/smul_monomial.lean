import Mathlib

variable {R : Type*}

variable [Semiring R] {p q : SkewPolynomial R}

variable {S S₁ S₂ : Type*}

theorem smul_monomial {S} [Semiring S] [Module S R] (a : S) (n : ℕ) (b : R) :
    a • SkewPolynomial.monomial n b = SkewPolynomial.monomial n (a • b) := smul_single ..

