import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'} {S : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J'.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
  (η : F.obj (unit R) ≅ unit S) (I : Type u) (i : I)
  [PreservesColimitsOfShape (Discrete I) F]

set_option backward.isDefEq.respectTransparency false in
theorem ιFree_mapFree_inv :
    SheafOfModules.ιFree i ≫ (SheafOfModules.mapFree F η I).inv = η.inv ≫ F.map (SheafOfModules.ιFree i) := by
  simp [SheafOfModules.mapFree, ← SheafOfModules.freeCofan_inj, Cofan.inj]

