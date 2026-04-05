import Mathlib

variable {C : Type _} [Category* C] [HasZeroMorphisms C]
  {S₁ S₂ S₃ S₄ : ShortComplex C}
  [S₁.HasHomology] [S₂.HasHomology] [S₃.HasHomology] [S₄.HasHomology]

theorem quasiIso_iff_isIso_rightHomologyMap' (φ : S₁ ⟶ S₂)
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    QuasiIso φ ↔ IsIso (rightHomologyMap' φ h₁ h₂) := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  rw [γ.quasiIso_iff, γ.rightHomologyMap'_eq]

