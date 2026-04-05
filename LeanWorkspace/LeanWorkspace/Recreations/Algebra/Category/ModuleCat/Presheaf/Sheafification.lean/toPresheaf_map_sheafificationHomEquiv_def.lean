import Mathlib

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

variable [HasWeakSheafify J AddCommGrpCat.{v}]

theorem toPresheaf_map_sheafificationHomEquiv_def
    {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v} R}
    (f : (PresheafOfModules.sheafification α).obj P ⟶ F) :
    (toPresheaf R₀).map (PresheafOfModules.sheafificationHomEquiv α f) =
      CategoryTheory.toSheafify J P.presheaf ≫ (toPresheaf R.obj).map f.val := rfl

