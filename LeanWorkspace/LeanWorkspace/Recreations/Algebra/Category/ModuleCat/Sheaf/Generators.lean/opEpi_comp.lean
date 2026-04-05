import Mathlib

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable (M N P : SheafOfModules.{u} R)

theorem opEpi_comp (σ : M.GeneratingSections) (p : M ⟶ N) (q : N ⟶ P) [Epi p] [Epi q] :
    σ.ofEpi (p ≫ q) = (σ.ofEpi p).ofEpi q := rfl

