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

theorem map_ιFree_mapFree_hom :
    F.map (SheafOfModules.ιFree i) ≫ (SheafOfModules.mapFree F η I).hom = η.hom ≫ SheafOfModules.ιFree i := by
  have : η.inv ≫ η.hom ≫ SheafOfModules.ιFree i = (η.inv ≫ F.map (SheafOfModules.ιFree i)) ≫ (SheafOfModules.mapFree F η I).hom := by
    simp [← SheafOfModules.ιFree_mapFree_inv]
  rw [← Iso.hom_inv_id_assoc η (η.hom ≫ SheafOfModules.ιFree i)]
  simp [this]

