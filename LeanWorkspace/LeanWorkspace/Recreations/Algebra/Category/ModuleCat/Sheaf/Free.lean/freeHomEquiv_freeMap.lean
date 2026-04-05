import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable {I J : Type u} (f : I → J)

theorem freeHomEquiv_freeMap :
    (SheafOfModules.freeHomEquiv _ (SheafOfModules.freeMap (R := R) f)) = freeSection.comp f :=
  (SheafOfModules.freeHomEquiv _).symm.injective (by simp; rfl)

