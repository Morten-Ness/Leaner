import Mathlib

variable {C : Type _} [Category* C] [HasZeroMorphisms C]
  {S₁ S₂ S₃ S₄ : ShortComplex C}
  [S₁.HasHomology] [S₂.HasHomology] [S₃.HasHomology] [S₄.HasHomology]

theorem quasiIso_of_comp_right (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃)
    [hφ' : QuasiIso φ'] [hφφ' : QuasiIso (φ ≫ φ')] :
    QuasiIso φ := by
  rw [CategoryTheory.ShortComplex.quasiIso_iff] at hφ' hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_right (homologyMap φ) (homologyMap φ')

