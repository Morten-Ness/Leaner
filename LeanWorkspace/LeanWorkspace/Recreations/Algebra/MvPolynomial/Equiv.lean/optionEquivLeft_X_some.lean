import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem optionEquivLeft_X_some (x : S₁) : MvPolynomial.optionEquivLeft R S₁ (Polynomial.X (some x)) = Polynomial.C (Polynomial.X x) := by
  simp [optionEquivLeft_apply, aeval_X]

