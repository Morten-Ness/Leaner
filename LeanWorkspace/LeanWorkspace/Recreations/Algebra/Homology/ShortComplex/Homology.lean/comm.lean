import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

theorem comm (h : CategoryTheory.ShortComplex.HomologyMapData φ h₁ h₂) :
    h.left.φH ≫ h₂.iso.hom = h₁.iso.hom ≫ h.right.φH := by
  simp only [← cancel_epi h₁.left.π, ← cancel_mono h₂.right.ι, assoc,
    LeftHomologyMapData.commπ_assoc, HomologyData.comm, LeftHomologyMapData.commi_assoc,
    RightHomologyMapData.commι, HomologyData.comm_assoc, RightHomologyMapData.commp]

