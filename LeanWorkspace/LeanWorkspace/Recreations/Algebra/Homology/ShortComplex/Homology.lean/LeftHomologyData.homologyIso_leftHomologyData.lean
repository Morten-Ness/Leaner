import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

set_option backward.isDefEq.respectTransparency false in
theorem LeftHomologyData.homologyIso_leftHomologyData [S.HasHomology] :
    S.leftHomologyData.homologyIso = S.leftHomologyIso.symm := by
  ext
  dsimp [homologyIso, CategoryTheory.ShortComplex.leftHomologyIso, CategoryTheory.ShortComplex.leftHomologyIso]
  rw [← leftHomologyMap'_comp, comp_id]

