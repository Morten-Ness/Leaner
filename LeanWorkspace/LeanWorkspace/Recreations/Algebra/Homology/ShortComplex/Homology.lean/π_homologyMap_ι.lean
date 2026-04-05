import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable (S) {A : C}

variable [HasHomology S]

theorem π_homologyMap_ι [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂) :
    S₁.homologyπ ≫ CategoryTheory.ShortComplex.homologyMap φ ≫ S₂.homologyι = S₁.iCycles ≫ φ.τ₂ ≫ S₂.pOpcycles := by
  simp only [CategoryTheory.ShortComplex.homologyι_naturality, homology_π_ι_assoc, p_opcyclesMap]

