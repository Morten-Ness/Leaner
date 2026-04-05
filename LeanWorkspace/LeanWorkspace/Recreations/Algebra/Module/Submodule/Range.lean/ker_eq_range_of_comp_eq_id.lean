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

theorem ker_eq_range_of_comp_eq_id {M P} [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] {f : M →ₗ[R] P} {g : P →ₗ[R] M} (h : f ∘ₗ g = .id) :
    ker f = LinearMap.range (LinearMap.id - g ∘ₗ f) := le_antisymm (fun x hx ↦ ⟨x, show x - g (f x) = x by rw [hx, map_zero, sub_zero]⟩) <|
    LinearMap.range_le_ker_iff.mpr <| by rw [comp_sub, comp_id, ← comp_assoc, h, id_comp, sub_self]

