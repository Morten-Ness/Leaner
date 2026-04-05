import Mathlib

variable {C : Type _} [Category* C] [HasZeroMorphisms C]
  {S₁ S₂ S₃ S₄ : ShortComplex C}
  [S₁.HasHomology] [S₂.HasHomology] [S₃.HasHomology] [S₄.HasHomology]

set_option backward.isDefEq.respectTransparency false in
theorem quasiIso_iff_isIso_descOpcycles (φ : S₁ ⟶ S₂)
    (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) :
    QuasiIso φ ↔ IsIso (S₁.descOpcycles φ.τ₂ (by rw [← φ.comm₁₂, hf₂, comp_zero])) := by
  let H : RightHomologyMapData φ
      (RightHomologyData.ofIsColimitCokernelCofork S₁ hg₁ _ S₁.opcyclesIsCokernel)
        (RightHomologyData.ofZeros S₂ hf₂ hg₂) :=
    { φQ := S₁.descOpcycles φ.τ₂ (by rw [← φ.comm₁₂, hf₂, comp_zero])
      φH := S₁.descOpcycles φ.τ₂ (by rw [← φ.comm₁₂, hf₂, comp_zero]) }
  exact H.quasiIso_iff

