import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem iterToSum_C_C (a : R) : MvPolynomial.iterToSum R S₁ S₂ (Polynomial.C (Polynomial.C a)) = Polynomial.C a := Eq.trans (eval₂_C _ _ (Polynomial.C a)) (eval₂_C _ _ _)

