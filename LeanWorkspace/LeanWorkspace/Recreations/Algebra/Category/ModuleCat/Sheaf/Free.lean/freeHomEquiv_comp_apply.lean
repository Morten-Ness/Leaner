import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

theorem freeHomEquiv_comp_apply {M N : SheafOfModules.{u} R} {I : Type u}
    (f : SheafOfModules.free I ⟶ M) (p : M ⟶ N) (i : I) :
    N.freeHomEquiv (f ≫ p) i = sectionsMap p (M.freeHomEquiv f i) := rfl

