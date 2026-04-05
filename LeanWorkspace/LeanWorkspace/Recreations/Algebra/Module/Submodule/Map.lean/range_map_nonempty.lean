import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable (p p' : Submodule R M) (q q' : Submodule R₂ M₂)

variable {x : M}

variable [RingHomSurjective σ₁₂]

theorem range_map_nonempty (N : Submodule R M) :
    (Set.range (fun ϕ => Submodule.map ϕ N : (M →ₛₗ[σ₁₂] M₂) → Submodule R₂ M₂)).Nonempty := ⟨_, Set.mem_range.mpr ⟨0, rfl⟩⟩

