import Mathlib

variable {C : Type _} [Category* C] [HasZeroMorphisms C]
  {S₁ S₂ S₃ S₄ : ShortComplex C}
  [S₁.HasHomology] [S₂.HasHomology] [S₃.HasHomology] [S₄.HasHomology]

theorem quasiIso_unopMap {S₁ S₂ : CategoryTheory.ShortComplex Cᵒᵖ} [S₁.HasHomology] [S₂.HasHomology]
    [S₁.unop.HasHomology] [S₂.unop.HasHomology]
    (φ : S₁ ⟶ S₂) [QuasiIso φ] : QuasiIso (unopMap φ) := by
  rw [← CategoryTheory.ShortComplex.quasiIso_opMap_iff]
  change QuasiIso φ
  infer_instance

