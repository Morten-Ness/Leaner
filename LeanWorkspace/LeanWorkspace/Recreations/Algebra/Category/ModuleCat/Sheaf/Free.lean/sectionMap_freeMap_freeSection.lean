import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable {I J : Type u} (f : I → J)

theorem sectionMap_freeMap_freeSection (i : I) :
    sectionsMap (SheafOfModules.freeMap (R := R) f) (freeSection i) = freeSection (f i) := by
  simp [← SheafOfModules.freeHomEquiv_comp_apply]

