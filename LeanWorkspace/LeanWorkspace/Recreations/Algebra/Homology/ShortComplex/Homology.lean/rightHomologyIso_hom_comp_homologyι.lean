import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable (S) {A : C}

variable [HasHomology S]

theorem rightHomologyIso_hom_comp_homologyι :
    S.rightHomologyIso.hom ≫ S.homologyι = S.rightHomologyι := by
  dsimp only [CategoryTheory.ShortComplex.homologyι]
  simp only [Iso.hom_inv_id_assoc]

