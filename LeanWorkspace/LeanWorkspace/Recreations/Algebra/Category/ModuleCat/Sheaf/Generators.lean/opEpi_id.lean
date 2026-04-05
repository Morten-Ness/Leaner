import Mathlib

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable (M N P : SheafOfModules.{u} R)

theorem opEpi_id (σ : M.GeneratingSections) :
    σ.ofEpi (𝟙 M) = σ := rfl

