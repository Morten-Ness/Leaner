import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}

variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

theorem ker_sup_ker_le_ker_comp_of_commute {f g : M →ₗ[R] M} (h : Commute f g) :
    LinearMap.ker f ⊔ LinearMap.ker g ≤ LinearMap.ker (f ∘ₗ g) := by
  refine sup_le_iff.mpr ⟨?_, LinearMap.ker_le_ker_comp g f⟩
  rw [← Module.End.mul_eq_comp, h.eq, Module.End.mul_eq_comp]
  exact LinearMap.ker_le_ker_comp f g

