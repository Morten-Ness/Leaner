import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

theorem freeHomEquiv_apply {M : SheafOfModules.{u} R} {I : Type u}
    (f : SheafOfModules.free I ⟶ M) (i : I) :
    SheafOfModules.freeHomEquiv M f i = sectionsMap f (freeSection i) := rfl

