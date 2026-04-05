import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable {A₁ A₂ A₃ : Type*} [CommSemiring A₁] [CommSemiring A₂] [CommSemiring A₃]

variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

theorem mapAlgEquiv_trans (e : A₁ ≃ₐ[R] A₂) (f : A₂ ≃ₐ[R] A₃) :
    (MvPolynomial.mapAlgEquiv σ e).trans (MvPolynomial.mapAlgEquiv σ f) = MvPolynomial.mapAlgEquiv σ (e.trans f) := by
  ext
  simp only [AlgEquiv.trans_apply, mapAlgEquiv_apply, map_map]
  rfl

