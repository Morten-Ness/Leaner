import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

theorem freeCofan_inj {I : Type u} (i : I) :
    (SheafOfModules.freeCofan (R := R) I).inj i = SheafOfModules.ιFree i := rfl

