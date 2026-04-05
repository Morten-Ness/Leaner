import Mathlib

variable {R L M : Type*}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable (Φ : LinearMap.BilinForm R M) (hΦ_nondeg : Φ.Nondegenerate)

theorem _root_.LinearMap.BilinForm.lieInvariant_iff [LieAlgebra R L] [LieModule R L M] :
    Φ.lieInvariant L ↔ Φ ∈ LieModule.maxTrivSubmodule R L (LinearMap.BilinForm R M) := by
  refine ⟨fun h x ↦ ?_, fun h x y z ↦ ?_⟩
  · ext y z
    rw [LieHom.lie_apply, LinearMap.sub_apply, Module.Dual.lie_apply, LinearMap.zero_apply,
      LinearMap.zero_apply, h, sub_self]
  · replace h := LinearMap.congr_fun₂ (h x) y z
    simp only [LieHom.lie_apply, LinearMap.sub_apply, Module.Dual.lie_apply,
      LinearMap.zero_apply, sub_eq_zero] at h
    simp [← h]

