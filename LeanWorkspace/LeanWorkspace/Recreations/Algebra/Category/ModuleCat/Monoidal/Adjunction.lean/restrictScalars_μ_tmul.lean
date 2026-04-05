import Mathlib

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
theorem restrictScalars_μ_tmul (M₁ M₂ : ModuleCat S) (m₁ : M₁) (m₂ : M₂) :
    dsimp% μ (restrictScalars f) M₁ M₂ (m₁ ⊗ₜ m₂) = m₁ ⊗ₜ m₂ := by
  dsimp [Adjunction.rightAdjointLaxMonoidal_μ]
  rw [extendRestrictScalarsAdj_homEquiv_apply]
  dsimp
  rw [ModuleCat.extendScalars_δ_tmul, tensorHom_tmul,
    extendRestrictScalarsAdj_counit_app_apply_one_tmul,
    extendRestrictScalarsAdj_counit_app_apply_one_tmul]

