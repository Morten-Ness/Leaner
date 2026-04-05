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

theorem comap_injective {f : M →ₛₗ[τ₁₂] M₂} (hf : LinearMap.range f = ⊤) : Function.Injective (comap f) := fun _ _ h =>
  le_antisymm ((LinearMap.comap_le_comap_iff hf).1 (le_of_eq h)) ((LinearMap.comap_le_comap_iff hf).1 (ge_of_eq h))

-- TODO (?): generalize the next two lemmas to semilinear maps with `f ∘ₗ g` bijective.

