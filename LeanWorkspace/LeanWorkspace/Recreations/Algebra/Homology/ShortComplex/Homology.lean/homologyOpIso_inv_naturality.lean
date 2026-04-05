import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

theorem homologyOpIso_inv_naturality [S₁.HasHomology] [S₂.HasHomology] :
    (CategoryTheory.ShortComplex.homologyMap φ).op ≫ (S₁.homologyOpIso).inv =
      S₂.homologyOpIso.inv ≫ CategoryTheory.ShortComplex.homologyMap (opMap φ) := by
  simp [CategoryTheory.ShortComplex.homologyMap_op]

