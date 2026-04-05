import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {X₁ X₂ X₃ X₄ : C} [HasBinaryBiproduct X₂ X₃]

variable {fst : X₁ ⟶ X₂} {snd : X₁ ⟶ X₃} {f : X₂ ⟶ X₄} {g : X₃ ⟶ X₄}

set_option backward.isDefEq.respectTransparency false in
theorem IsPullback.mono_shortComplex'_f (h : IsPullback fst snd f g) :
    Mono h.shortComplex'.f := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro _ b hb
  exact Fork.IsLimit.hom_ext h.isLimitKernelFork (by simpa using hb)

