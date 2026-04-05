import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem rightHomologyMap'_op
    (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    (CategoryTheory.ShortComplex.rightHomologyMap' φ h₁ h₂).op = leftHomologyMap' (opMap φ) h₂.op h₁.op := by
  let γ : RightHomologyMapData φ h₁ h₂ := CategoryTheory.ShortComplex.rightHomologyMapData φ h₁ h₂
  simp only [γ.rightHomologyMap'_eq, γ.op.leftHomologyMap'_eq,
    RightHomologyMapData.op_φH]

