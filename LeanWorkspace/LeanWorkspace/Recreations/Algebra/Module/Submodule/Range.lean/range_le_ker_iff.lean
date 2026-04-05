import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}

variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

variable [RingHomSurjective τ₁₂]

theorem range_le_ker_iff {f : M →ₛₗ[τ₁₂] M₂} {g : M₂ →ₛₗ[τ₂₃] M₃} :
    LinearMap.range f ≤ ker g ↔ (g.comp f : M →ₛₗ[τ₁₃] M₃) = 0 := ⟨fun h => ker_eq_top.1 <| eq_top_iff'.2 fun _ => h <| ⟨_, rfl⟩, fun h x hx =>
    mem_ker.2 <| Exists.elim hx fun y hy => by rw [← hy, ← comp_apply, h, zero_apply]⟩

