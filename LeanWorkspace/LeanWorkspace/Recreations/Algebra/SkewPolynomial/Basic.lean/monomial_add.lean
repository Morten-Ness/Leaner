import Mathlib

variable {R : Type*}

variable [Semiring R] {p q : SkewPolynomial R}

variable {S S₁ S₂ : Type*}

theorem monomial_add (n : ℕ) (r s : R) :
    SkewPolynomial.monomial n (r + s) = SkewPolynomial.monomial n r + SkewPolynomial.monomial n s := single_add ..

