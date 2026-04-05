import Mathlib

variable {C : Type _} [Category* C] [HasZeroMorphisms C]
  {S₁ S₂ S₃ S₄ : ShortComplex C}
  [S₁.HasHomology] [S₂.HasHomology] [S₃.HasHomology] [S₄.HasHomology]

theorem quasiIso_iff_isIso_leftHomologyMap' (φ : S₁ ⟶ S₂)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    QuasiIso φ ↔ IsIso (leftHomologyMap' φ h₁ h₂) := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  rw [γ.quasiIso_iff, γ.leftHomologyMap'_eq]

