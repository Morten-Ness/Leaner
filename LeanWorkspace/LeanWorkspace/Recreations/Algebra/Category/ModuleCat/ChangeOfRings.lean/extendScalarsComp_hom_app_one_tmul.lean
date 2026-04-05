import Mathlib

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

variable {R₁ R₂ R₃ R₄ : Type u₁} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]
  (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) (f₃₄ : R₃ →+* R₄)

set_option backward.isDefEq.respectTransparency false in
theorem extendScalarsComp_hom_app_one_tmul (M : ModuleCat R₁) (m : M) :
    (ModuleCat.extendScalarsComp f₁₂ f₂₃).hom.app M ((1 : R₃) ⊗ₜ m) =
      (1 : R₃) ⊗ₜ[R₂,f₂₃] ((1 : R₂) ⊗ₜ[R₁,f₁₂] m) := by
  rw [← ModuleCat.extendRestrictScalarsAdj_homEquiv_apply, ModuleCat.homEquiv_extendScalarsComp]
  rfl

