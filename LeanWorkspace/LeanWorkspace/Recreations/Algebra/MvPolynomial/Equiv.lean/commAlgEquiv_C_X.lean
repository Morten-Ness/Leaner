import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable {R S₁ S₂ : Type*} [CommSemiring R]

theorem commAlgEquiv_C_X (i) : MvPolynomial.commAlgEquiv R S₁ S₂ (.C (.X i)) = .X i := by simp

