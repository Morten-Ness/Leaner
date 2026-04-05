import Mathlib

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

variable {R₁ R₂ R₃ R₄ : Type u₁} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]
  (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) (f₃₄ : R₃ →+* R₄)

theorem extendScalars_comp_id :
    (ModuleCat.extendScalarsComp f₁₂ (RingHom.id R₂)).hom ≫ Functor.whiskerLeft _ (ModuleCat.extendScalarsId R₂).hom ≫
      (Functor.rightUnitor _).hom = 𝟙 _ := by
  ext M m
  dsimp
  erw [ModuleCat.extendScalarsComp_hom_app_one_tmul f₁₂ (RingHom.id R₂) M m,
    ModuleCat.extendScalarsId_hom_app_one_tmul]
  rfl

