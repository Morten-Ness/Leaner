import Mathlib

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

variable {R₁ R₂ R₃ R₄ : Type u₁} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]
  (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) (f₃₄ : R₃ →+* R₄)

set_option backward.isDefEq.respectTransparency false in
theorem extendScalars_assoc :
    (ModuleCat.extendScalarsComp (f₂₃.comp f₁₂) f₃₄).hom ≫
      Functor.whiskerRight (ModuleCat.extendScalarsComp f₁₂ f₂₃).hom _ =
        (ModuleCat.extendScalarsComp f₁₂ (f₃₄.comp f₂₃)).hom ≫
          Functor.whiskerLeft _ (ModuleCat.extendScalarsComp f₂₃ f₃₄).hom ≫
            (Functor.associator _ _ _).inv := by
  ext M m
  have h₁ := ModuleCat.extendScalarsComp_hom_app_one_tmul (f₂₃.comp f₁₂) f₃₄ M m
  have h₂ := ModuleCat.extendScalarsComp_hom_app_one_tmul f₁₂ (f₃₄.comp f₂₃) M m
  have h₃ := ModuleCat.extendScalarsComp_hom_app_one_tmul f₂₃ f₃₄
  have h₄ := ModuleCat.extendScalarsComp_hom_app_one_tmul f₁₂ f₂₃ M m
  dsimp at h₁ h₂ h₃ h₄ ⊢
  rw [h₁]
  erw [h₂]
  rw [h₃, ExtendScalars.map_tmul, h₄]

