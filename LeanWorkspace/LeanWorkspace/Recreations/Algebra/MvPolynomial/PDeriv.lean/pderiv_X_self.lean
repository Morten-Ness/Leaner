import Mathlib

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

variable [CommSemiring R]

theorem pderiv_X_self (i : σ) : MvPolynomial.pderiv i (X i : MvPolynomial σ R) = 1 := by classical simp

