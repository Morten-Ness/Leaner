import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable [IsDomain R₂] [Module.Free R₂ M₂] [Module.Finite R₂ M₂] {B : BilinForm R₂ M₂}

theorem nondegenerate_iff_ker_eq_bot : B.Nondegenerate ↔ B.ker = ⊥ := by
  refine ⟨Nondegenerate.ker_eq_bot, fun h ↦ .ofSeparatingLeft ?_⟩
  rwa [separatingLeft_iff_ker_eq_bot]

