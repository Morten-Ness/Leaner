import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem sumToIter_Xl (b : S₁) : MvPolynomial.sumToIter R S₁ S₂ (Polynomial.X (Sum.inl b)) = Polynomial.X b := eval₂_X _ _ (Sum.inl b)

