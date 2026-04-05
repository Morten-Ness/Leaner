import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {R S σ τ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

theorem Polynomial.toMvPolynomial_X (i : σ) : Polynomial.X.toMvPolynomial i = MvPolynomial.X (R := R) i := by
  simp [toMvPolynomial]

