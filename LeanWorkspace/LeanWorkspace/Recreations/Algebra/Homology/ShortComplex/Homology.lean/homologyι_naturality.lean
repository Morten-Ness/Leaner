import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable (S) {A : C}

variable [HasHomology S]

theorem homologyι_naturality (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] :
    CategoryTheory.ShortComplex.homologyMap φ ≫ S₂.homologyι = S₁.homologyι ≫ S₁.opcyclesMap φ := by
  simp only [← cancel_epi S₁.rightHomologyIso.hom, rightHomologyIso_hom_naturality_assoc φ,
    CategoryTheory.ShortComplex.rightHomologyIso_hom_comp_homologyι, rightHomologyι_naturality]
  simp only [CategoryTheory.ShortComplex.homologyι, assoc, Iso.hom_inv_id_assoc]

