import Mathlib

variable {C : Type _} [Category* C] [HasZeroMorphisms C]
  {S₁ S₂ S₃ S₄ : ShortComplex C}
  [S₁.HasHomology] [S₂.HasHomology] [S₃.HasHomology] [S₄.HasHomology]

theorem quasiIso_opMap (φ : S₁ ⟶ S₂) [QuasiIso φ] :
    QuasiIso (opMap φ) := by
  rw [CategoryTheory.ShortComplex.quasiIso_opMap_iff]
  infer_instance

