import Mathlib

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

