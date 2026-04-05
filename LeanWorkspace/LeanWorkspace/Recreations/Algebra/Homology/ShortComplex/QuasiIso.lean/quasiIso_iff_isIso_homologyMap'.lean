import Mathlib

variable {C : Type _} [Category* C] [HasZeroMorphisms C]
  {S₁ S₂ S₃ S₄ : ShortComplex C}
  [S₁.HasHomology] [S₂.HasHomology] [S₃.HasHomology] [S₄.HasHomology]

theorem quasiIso_iff_isIso_homologyMap' (φ : S₁ ⟶ S₂)
    (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
    QuasiIso φ ↔ IsIso (homologyMap' φ h₁ h₂) := CategoryTheory.ShortComplex.quasiIso_iff_isIso_leftHomologyMap' _ _ _

