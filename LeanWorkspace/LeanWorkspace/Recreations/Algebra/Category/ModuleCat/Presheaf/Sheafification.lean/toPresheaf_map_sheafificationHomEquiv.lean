import Mathlib

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

