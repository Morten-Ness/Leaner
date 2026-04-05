import Mathlib

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

variable [HasWeakSheafify J AddCommGrpCat.{v}]

theorem toPresheaf_map_sheafificationAdjunction_unit_app (M₀ : PresheafOfModules.{v} R₀) :
    (toPresheaf _).map ((PresheafOfModules.sheafificationAdjunction α).unit.app M₀) =
      CategoryTheory.toSheafify J M₀.presheaf := rfl

