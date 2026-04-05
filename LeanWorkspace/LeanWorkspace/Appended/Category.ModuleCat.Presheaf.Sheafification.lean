import Mathlib

section

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

variable [HasWeakSheafify J AddCommGrpCat.{v}]

set_option backward.isDefEq.respectTransparency false in
theorem toPresheaf_map_sheafificationHomEquiv
    {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v} R}
    (f : (PresheafOfModules.sheafification α).obj P ⟶ F) :
    (toPresheaf R₀).map (PresheafOfModules.sheafificationHomEquiv α f) =
      (sheafificationAdjunction J AddCommGrpCat).homEquiv P.presheaf
        ((SheafOfModules.toSheaf _).obj F) ((SheafOfModules.toSheaf _).map f) := by
  rw [PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def, Adjunction.homEquiv_unit]
  dsimp

end

section

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

variable [HasWeakSheafify J AddCommGrpCat.{v}]

theorem toSheaf_map_sheafificationAdjunction_counit_app (M : SheafOfModules.{v} R) :
    (SheafOfModules.toSheaf R).map ((PresheafOfModules.sheafificationAdjunction α).counit.app M) =
      (CategoryTheory.sheafificationAdjunction J
          AddCommGrpCat.{v}).counit.app ((SheafOfModules.toSheaf R).obj M) := (PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm _ _).trans
    (by rw [← Adjunction.homEquiv_symm_id]; rfl)

end

section

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

variable [HasWeakSheafify J AddCommGrpCat.{v}]

theorem toSheaf_map_sheafificationHomEquiv_symm
    {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v} R}
    (g : P ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F)) :
    (SheafOfModules.toSheaf _).map ((PresheafOfModules.sheafificationHomEquiv α).symm g) =
      (((sheafificationAdjunction J AddCommGrpCat).homEquiv
        P.presheaf ((SheafOfModules.toSheaf R).obj F)).symm ((toPresheaf R₀).map g)) := by
  obtain ⟨f, rfl⟩ := (PresheafOfModules.sheafificationHomEquiv α).surjective g
  apply ((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Equiv.symm_apply_apply]
  rfl

end
