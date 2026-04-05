import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂)

set_option backward.isDefEq.respectTransparency false in
theorem LeftHomologyData.leftHomologyIso_inv_naturality
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    h₁.homologyIso.inv ≫ CategoryTheory.ShortComplex.homologyMap φ =
      leftHomologyMap' φ h₁ h₂ ≫ h₂.homologyIso.inv := by
  dsimp [homologyIso, CategoryTheory.ShortComplex.leftHomologyIso, CategoryTheory.ShortComplex.homologyMap, CategoryTheory.ShortComplex.homologyMap', CategoryTheory.ShortComplex.leftHomologyIso]
  simp only [← leftHomologyMap'_comp, id_comp, comp_id]

