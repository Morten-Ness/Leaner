import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem optionEquivLeft_symm_C_C (x : R) :
    (MvPolynomial.optionEquivLeft R S₁).symm (.C (.C x)) = .C x := by simp [MvPolynomial.optionEquivLeft]

