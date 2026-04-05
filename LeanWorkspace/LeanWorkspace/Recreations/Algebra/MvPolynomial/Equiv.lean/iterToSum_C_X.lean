import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem iterToSum_C_X (c : S₂) : MvPolynomial.iterToSum R S₁ S₂ (Polynomial.C (Polynomial.X c)) = Polynomial.X (Sum.inr c) := Eq.trans (eval₂_C _ _ (Polynomial.X c)) (eval₂_X _ _ _)

