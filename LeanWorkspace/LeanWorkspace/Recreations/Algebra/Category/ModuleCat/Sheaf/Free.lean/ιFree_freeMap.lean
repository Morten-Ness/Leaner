import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable {I J : Type u} (f : I → J)

theorem ιFree_freeMap (i : I) :
    SheafOfModules.ιFree (R := R) i ≫ SheafOfModules.freeMap f = SheafOfModules.ιFree (f i) := by
  rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply, SheafOfModules.freeHomEquiv_freeMap]
  dsimp [freeSection]
  rw [SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply, Category.comp_id]

