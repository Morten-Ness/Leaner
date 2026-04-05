import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData)

theorem opcyclesMap'_g' : CategoryTheory.ShortComplex.opcyclesMap' φ h₁ h₂ ≫ h₂.g' = h₁.g' ≫ φ.τ₃ := by
  simp only [← cancel_epi h₁.p, φ.comm₂₃, p_opcyclesMap'_assoc,
    RightHomologyData.p_g'_assoc, RightHomologyData.p_g']

