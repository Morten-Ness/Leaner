import Mathlib

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

variable {R₁ R₂ R₃ R₄ : Type u₁} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]
  (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) (f₃₄ : R₃ →+* R₄)

set_option backward.isDefEq.respectTransparency false in
theorem extendScalars_assoc' :
    (ModuleCat.extendScalarsComp (f₂₃.comp f₁₂) f₃₄).hom ≫
      Functor.whiskerRight (ModuleCat.extendScalarsComp f₁₂ f₂₃).hom _ ≫
        (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft _ (ModuleCat.extendScalarsComp f₂₃ f₃₄).inv ≫
            (ModuleCat.extendScalarsComp f₁₂ (f₃₄.comp f₂₃)).inv = 𝟙 _ := by
  rw [extendScalars_assoc_assoc]
  simp only [Iso.inv_hom_id_assoc, ← Functor.whiskerLeft_comp_assoc, Iso.hom_inv_id,
    Functor.whiskerLeft_id', Category.id_comp]

