import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasDerivedCategory.{w} C]

theorem singleFunctorsPostcompQIso_hom_hom (n : ℤ) :
    (DerivedCategory.singleFunctorsPostcompQIso C).hom.hom n = 𝟙 _ := by
  ext X
  dsimp [DerivedCategory.singleFunctorsPostcompQIso, HomotopyCategory.singleFunctorsPostcompQuotientIso,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.id_comp]
  rfl

