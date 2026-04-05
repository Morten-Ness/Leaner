import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable {I J : Type u} (f : I → J)

theorem sectionsMap_freeHomEquiv_symm_freeSection
    {M : SheafOfModules.{u} R} (f : I → M.sections) (i : I) :
    sectionsMap ((SheafOfModules.freeHomEquiv M).symm f) (freeSection i) = f i := by
  obtain ⟨f, rfl⟩ := (SheafOfModules.freeHomEquiv M).surjective f
  cat_disch

