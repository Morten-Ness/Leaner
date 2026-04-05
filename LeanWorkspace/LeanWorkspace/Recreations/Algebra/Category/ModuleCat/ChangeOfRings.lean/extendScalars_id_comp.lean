import Mathlib

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

variable {R₁ R₂ R₃ R₄ : Type u₁} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]
  (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) (f₃₄ : R₃ →+* R₄)

set_option backward.isDefEq.respectTransparency false in
theorem extendScalars_id_comp :
    (ModuleCat.extendScalarsComp (RingHom.id R₁) f₁₂).hom ≫ Functor.whiskerRight (ModuleCat.extendScalarsId R₁).hom _ ≫
      (Functor.leftUnitor _).hom = 𝟙 _ := by
  ext M m
  dsimp
  erw [ModuleCat.extendScalarsComp_hom_app_one_tmul (RingHom.id R₁) f₁₂ M m]
  rw [ExtendScalars.map_tmul]
  erw [ModuleCat.extendScalarsId_hom_app_one_tmul]
  rfl

