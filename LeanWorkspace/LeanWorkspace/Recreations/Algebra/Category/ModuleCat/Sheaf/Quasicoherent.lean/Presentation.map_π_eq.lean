import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)] {ι σ : Type u}

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'} {S : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [J'.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

variable {M : SheafOfModules.{u} R} (P : Presentation M)
  (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S) [PreservesColimitsOfSize.{u, u} F]
  (η : F.obj (unit R) ≅ unit S)

theorem Presentation.map_π_eq :
    (P.map F η).generators.π = (mapFree F η _).inv ≫ F.map (P.generators.π) := (F.obj M).freeHomEquiv.symm_apply_eq.mpr rfl

