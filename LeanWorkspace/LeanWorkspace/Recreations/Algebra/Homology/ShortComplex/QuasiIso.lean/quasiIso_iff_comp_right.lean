import Mathlib

variable {C : Type _} [Category* C] [HasZeroMorphisms C]
  {S₁ S₂ S₃ S₄ : ShortComplex C}
  [S₁.HasHomology] [S₂.HasHomology] [S₃.HasHomology] [S₄.HasHomology]

theorem quasiIso_iff_comp_right (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [hφ' : QuasiIso φ'] :
    QuasiIso (φ ≫ φ') ↔ QuasiIso φ := by
  constructor
  · intro
    exact CategoryTheory.ShortComplex.quasiIso_of_comp_right φ φ'
  · intro
    exact quasiIso_comp φ φ'

