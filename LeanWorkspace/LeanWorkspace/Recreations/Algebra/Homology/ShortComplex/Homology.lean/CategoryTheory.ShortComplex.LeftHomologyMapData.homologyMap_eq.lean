import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
  (γ : LeftHomologyMapData φ h₁ h₂) [S₁.HasHomology] [S₂.HasHomology]

set_option backward.isDefEq.respectTransparency false in
theorem homologyMap_eq :
    CategoryTheory.ShortComplex.homologyMap φ = h₁.homologyIso.hom ≫ γ.φH ≫ h₂.homologyIso.inv := by
  dsimp [CategoryTheory.ShortComplex.homologyMap, CategoryTheory.ShortComplex.LeftHomologyData.homologyIso, CategoryTheory.ShortComplex.leftHomologyIso,
    LeftHomologyData.leftHomologyIso, CategoryTheory.ShortComplex.homologyMap']
  simp only [← γ.leftHomologyMap'_eq, ← leftHomologyMap'_comp, id_comp, comp_id]

