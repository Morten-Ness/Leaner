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

theorem disjoint_iff_comap_eq_bot {p q : Submodule R M} : Disjoint p q ↔ Submodule.comap p.subtype q = ⊥ := by
  rw [← (Submodule.map_injective_of_injective (show Function.Injective p.subtype from Subtype.coe_injective)).eq_iff,
    Submodule.map_comap_subtype, Submodule.map_bot, disjoint_iff]

