import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable {A₁ A₂ A₃ : Type*} [CommSemiring A₁] [CommSemiring A₂] [CommSemiring A₃]

variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

theorem mapAlgEquiv_symm (e : A₁ ≃ₐ[R] A₂) : (MvPolynomial.mapAlgEquiv σ e).symm = MvPolynomial.mapAlgEquiv σ e.symm := rfl

