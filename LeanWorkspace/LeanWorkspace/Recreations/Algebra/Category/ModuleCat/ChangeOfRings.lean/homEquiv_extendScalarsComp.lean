import Mathlib

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

variable {R₁ R₂ R₃ R₄ : Type u₁} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]
  (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) (f₃₄ : R₃ →+* R₄)

set_option backward.isDefEq.respectTransparency false in
theorem homEquiv_extendScalarsComp (M : ModuleCat R₁) :
    (ModuleCat.extendRestrictScalarsAdj (f₂₃.comp f₁₂)).homEquiv _ _
      ((ModuleCat.extendScalarsComp f₁₂ f₂₃).hom.app M) =
      (ModuleCat.extendRestrictScalarsAdj f₁₂).unit.app M ≫
        (ModuleCat.restrictScalars f₁₂).map ((ModuleCat.extendRestrictScalarsAdj f₂₃).unit.app _) ≫
        (restrictScalarsComp f₁₂ f₂₃).inv.app _ := by
  dsimp [ModuleCat.extendScalarsComp, conjugateIsoEquiv, conjugateEquiv]
  simp only [Category.assoc, Category.id_comp, Category.comp_id,
    Adjunction.comp_unit_app, Adjunction.homEquiv_unit,
    Functor.map_comp, Adjunction.unit_naturality_assoc,
    Adjunction.right_triangle_components]
  rfl

