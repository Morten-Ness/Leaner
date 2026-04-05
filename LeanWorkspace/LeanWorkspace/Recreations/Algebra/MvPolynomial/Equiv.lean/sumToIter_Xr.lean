import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem sumToIter_Xr (c : S₂) : MvPolynomial.sumToIter R S₁ S₂ (Polynomial.X (Sum.inr c)) = Polynomial.C (Polynomial.X c) := eval₂_X _ _ (Sum.inr c)

