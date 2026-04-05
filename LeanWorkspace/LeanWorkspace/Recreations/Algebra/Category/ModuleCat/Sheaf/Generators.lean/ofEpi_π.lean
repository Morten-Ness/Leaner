import Mathlib

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable (M N P : SheafOfModules.{u} R)

theorem ofEpi_π (σ : M.GeneratingSections) (p : M ⟶ N) [Epi p] :
    (σ.ofEpi p).π = σ.π ≫ p := by
  simp [SheafOfModules.GeneratingSections.ofEpi, freeHomEquiv_symm_comp]

