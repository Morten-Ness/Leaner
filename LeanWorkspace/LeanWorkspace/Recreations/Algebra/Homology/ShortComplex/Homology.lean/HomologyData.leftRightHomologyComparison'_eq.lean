import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

theorem HomologyData.leftRightHomologyComparison'_eq (h : S.HomologyData) :
    CategoryTheory.ShortComplex.leftRightHomologyComparison' h.left h.right = h.iso.hom := by
  simp only [← cancel_epi h.left.π, ← cancel_mono h.right.ι, assoc,
    CategoryTheory.ShortComplex.π_leftRightHomologyComparison'_ι, CategoryTheory.ShortComplex.HomologyMapData.comm]

