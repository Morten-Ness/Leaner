import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

theorem leftRightHomologyComparison'_naturality (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData)
    (h₂ : S₁.RightHomologyData) (h₁' : S₂.LeftHomologyData) (h₂' : S₂.RightHomologyData) :
    leftHomologyMap' φ h₁ h₁' ≫ CategoryTheory.ShortComplex.leftRightHomologyComparison' h₁' h₂' =
      CategoryTheory.ShortComplex.leftRightHomologyComparison' h₁ h₂ ≫ rightHomologyMap' φ h₂ h₂' := by
  simp only [← cancel_epi h₁.π, ← cancel_mono h₂'.ι, assoc,
    leftHomologyπ_naturality'_assoc, rightHomologyι_naturality',
    CategoryTheory.ShortComplex.π_leftRightHomologyComparison'_ι, π_leftRightHomologyComparison'_ι_assoc,
    cyclesMap'_i_assoc, p_opcyclesMap']

