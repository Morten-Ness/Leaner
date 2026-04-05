import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

theorem unitHomEquiv_symm_freeHomEquiv_apply
    {I : Type u} {M : SheafOfModules.{u} R} (f : SheafOfModules.free I ⟶ M) (i : I) :
    M.unitHomEquiv.symm (M.freeHomEquiv f i) = SheafOfModules.ιFree i ≫ f := by
  simp [SheafOfModules.freeHomEquiv]

