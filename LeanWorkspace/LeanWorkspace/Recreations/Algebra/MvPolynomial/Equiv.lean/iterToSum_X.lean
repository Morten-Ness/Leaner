import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem iterToSum_X (b : S₁) : MvPolynomial.iterToSum R S₁ S₂ (Polynomial.X b) = Polynomial.X (Sum.inl b) := eval₂_X _ _ _

