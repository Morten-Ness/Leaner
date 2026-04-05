import Mathlib

variable {C : Type _} [Category* C] [HasZeroMorphisms C]
  {S₁ S₂ S₃ S₄ : ShortComplex C}
  [S₁.HasHomology] [S₂.HasHomology] [S₃.HasHomology] [S₄.HasHomology]

theorem quasiIso_iff (φ : S₁ ⟶ S₂) :
    QuasiIso φ ↔ IsIso (homologyMap φ) := by
  constructor
  · intro h
    infer_instance
  · intro h
    exact ⟨h⟩

