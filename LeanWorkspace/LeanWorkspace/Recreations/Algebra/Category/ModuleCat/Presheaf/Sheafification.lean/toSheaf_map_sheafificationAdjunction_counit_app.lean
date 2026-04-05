import Mathlib

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

