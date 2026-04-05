import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {R S σ τ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

theorem Polynomial.toMvPolynomial_C (i : σ) (r : R) : (Polynomial.C r).toMvPolynomial i = MvPolynomial.C r := by
  simp [toMvPolynomial]

