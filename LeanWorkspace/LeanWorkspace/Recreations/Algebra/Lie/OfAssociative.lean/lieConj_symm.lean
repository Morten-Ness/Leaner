import Mathlib

variable {R : Type u} {M₁ : Type v} {M₂ : Type w}

variable [CommRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

variable (e : M₁ ≃ₗ[R] M₂)

theorem lieConj_symm : e.lieConj.symm = e.symm.lieConj := rfl

