import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
  (γ : RightHomologyMapData φ h₁ h₂) [S₁.HasHomology] [S₂.HasHomology]

set_option backward.isDefEq.respectTransparency false in
theorem homologyMap_eq :
    CategoryTheory.ShortComplex.homologyMap φ = h₁.homologyIso.hom ≫ γ.φH ≫ h₂.homologyIso.inv := by
  dsimp [CategoryTheory.ShortComplex.homologyMap, CategoryTheory.ShortComplex.homologyMap', CategoryTheory.ShortComplex.RightHomologyData.homologyIso,
    CategoryTheory.ShortComplex.rightHomologyIso, RightHomologyData.rightHomologyIso]
  have γ' : HomologyMapData φ S₁.homologyData S₂.homologyData := default
  simp only [← γ.rightHomologyMap'_eq, assoc, ← rightHomologyMap'_comp_assoc,
    id_comp, comp_id, γ'.left.leftHomologyMap'_eq, γ'.right.rightHomologyMap'_eq, ← γ'.comm_assoc,
    Iso.hom_inv_id]

