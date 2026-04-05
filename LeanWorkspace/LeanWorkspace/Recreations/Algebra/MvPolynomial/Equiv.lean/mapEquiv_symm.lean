import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem mapEquiv_symm [CommSemiring S₁] [CommSemiring S₂] (e : S₁ ≃+* S₂) :
    (MvPolynomial.mapEquiv σ e).symm = MvPolynomial.mapEquiv σ e.symm := rfl

