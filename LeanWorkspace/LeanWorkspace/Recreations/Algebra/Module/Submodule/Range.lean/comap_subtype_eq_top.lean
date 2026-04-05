import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R₂ M₂]

variable (p : Submodule R M)

variable {τ₁₂ : R →+* R₂}

theorem comap_subtype_eq_top {p p' : Submodule R M} : comap p.subtype p' = ⊤ ↔ p ≤ p' := eq_top_iff.trans <| map_le_iff_le_comap.symm.trans <| by rw [Submodule.map_subtype_top]

