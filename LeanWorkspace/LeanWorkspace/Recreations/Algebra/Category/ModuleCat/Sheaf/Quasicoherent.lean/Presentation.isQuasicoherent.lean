import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

variable {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat]

theorem Presentation.isQuasicoherent {M : SheafOfModules.{u} R} (P : Presentation M) :
    IsQuasicoherent M where
  nonempty_quasicoherentData := Nonempty.intro (Presentation.quasicoherentData P)

