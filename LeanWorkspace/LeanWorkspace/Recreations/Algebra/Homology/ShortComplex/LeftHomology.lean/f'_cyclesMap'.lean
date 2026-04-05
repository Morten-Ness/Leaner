import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)

theorem f'_cyclesMap' : h₁.f' ≫ CategoryTheory.ShortComplex.cyclesMap' φ h₁ h₂ = φ.τ₁ ≫ h₂.f' := by
  simp only [← cancel_mono h₂.i, assoc, φ.comm₁₂, CategoryTheory.ShortComplex.cyclesMap'_i,
    LeftHomologyData.f'_i_assoc, LeftHomologyData.f'_i]

