import Mathlib

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

variable [CommSemiring R]

theorem pderiv_X_of_ne {i j : σ} (h : j ≠ i) : MvPolynomial.pderiv i (X j : MvPolynomial σ R) = 0 := by
  classical simp [h]

