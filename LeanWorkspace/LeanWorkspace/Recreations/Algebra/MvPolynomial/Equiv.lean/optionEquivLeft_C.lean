import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem optionEquivLeft_C (r : R) : MvPolynomial.optionEquivLeft R S₁ (Polynomial.C r) = Polynomial.C (Polynomial.C r) := by
  simp only [optionEquivLeft_apply, aeval_C, Polynomial.algebraMap_apply, algebraMap_eq]

