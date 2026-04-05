import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem optionEquivRight_C (r : R) : MvPolynomial.optionEquivRight R S₁ (Polynomial.C r) = Polynomial.C (Polynomial.C r) := by
  simp only [optionEquivRight_apply, aeval_C, algebraMap_apply, Polynomial.algebraMap_eq]

