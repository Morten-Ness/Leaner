import Mathlib

variable {C : Type _} [Category* C] [HasZeroMorphisms C]
  {S₁ S₂ S₃ S₄ : ShortComplex C}
  [S₁.HasHomology] [S₂.HasHomology] [S₃.HasHomology] [S₄.HasHomology]

set_option backward.isDefEq.respectTransparency false in
theorem quasiIso_iff_isIso_liftCycles (φ : S₁ ⟶ S₂)
    (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) :
    QuasiIso φ ↔ IsIso (S₂.liftCycles φ.τ₂ (by rw [φ.comm₂₃, hg₁, zero_comp])) := by
  let H : LeftHomologyMapData φ (LeftHomologyData.ofZeros S₁ hf₁ hg₁)
      (LeftHomologyData.ofIsLimitKernelFork S₂ hf₂ _ S₂.cyclesIsKernel) :=
    { φK := S₂.liftCycles φ.τ₂ (by rw [φ.comm₂₃, hg₁, zero_comp])
      φH := S₂.liftCycles φ.τ₂ (by rw [φ.comm₂₃, hg₁, zero_comp]) }
  exact H.quasiIso_iff

