import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable (S) {A : C}

variable [HasHomology S]

theorem homologyπ_naturality (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] :
    S₁.homologyπ ≫ CategoryTheory.ShortComplex.homologyMap φ = cyclesMap φ ≫ S₂.homologyπ := by
  simp only [← cancel_mono S₂.leftHomologyIso.inv, assoc, ← CategoryTheory.ShortComplex.leftHomologyIso_inv_naturality φ,
    CategoryTheory.ShortComplex.homologyπ_comp_leftHomologyIso_inv]
  simp only [CategoryTheory.ShortComplex.homologyπ, assoc, Iso.hom_inv_id_assoc, leftHomologyπ_naturality]

