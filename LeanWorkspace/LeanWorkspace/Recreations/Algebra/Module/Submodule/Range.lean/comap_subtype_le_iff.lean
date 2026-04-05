import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R₂ M₂]

variable (p : Submodule R M)

variable {τ₁₂ : R →+* R₂}

theorem comap_subtype_le_iff {p q r : Submodule R M} :
    q.comap p.subtype ≤ r.comap p.subtype ↔ p ⊓ q ≤ p ⊓ r := ⟨fun h ↦ by simpa using map_mono (f := p.subtype) h,
   fun h ↦ by simpa using comap_mono (f := p.subtype) h⟩

