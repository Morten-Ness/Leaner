import Mathlib

variable {R : Type*}

variable [Semiring R] {p q : SkewPolynomial R}

variable {S S₁ S₂ : Type*}

theorem monomial_mul_monomial [MulSemiringAction (Multiplicative ℕ) R] (n m : ℕ) (r s : R) :
    SkewPolynomial.monomial n r * SkewPolynomial.monomial m s = SkewPolynomial.monomial (n + m) (r * (φ^[n] s)) := by
  rw [SkewPolynomial.φ_iterate_apply]
  exact SkewMonoidAlgebra.single_mul_single

