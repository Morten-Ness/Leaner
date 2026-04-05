import Mathlib

section

variable {C : Type*} [Category* C] [Preadditive C]
  {X₁ X₂ X₃ X₄ : C} [HasBinaryBiproduct X₂ X₃]

variable {fst : X₁ ⟶ X₂} {snd : X₁ ⟶ X₃} {f : X₂ ⟶ X₄} {g : X₃ ⟶ X₄}

set_option backward.isDefEq.respectTransparency false in
theorem IsPullback.mono_shortComplex'_f (h : IsPullback fst snd f g) :
    Mono h.shortComplex'.f := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro _ b hb
  exact Fork.IsLimit.hom_ext h.isLimitKernelFork (by simpa using hb)

end

section

variable {C : Type*} [Category* C] [Preadditive C]
  {X₁ X₂ X₃ X₄ : C} [HasBinaryBiproduct X₂ X₃]

variable {f : X₁ ⟶ X₂} {g : X₁ ⟶ X₃} {inl : X₂ ⟶ X₄} {inr : X₃ ⟶ X₄}

set_option backward.isDefEq.respectTransparency false in
theorem IsPushout.epi_shortComplex_g (h : IsPushout f g inl inr) :
    Epi h.shortComplex.g := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro _ b hb
  exact Cofork.IsColimit.hom_ext h.isColimitCokernelCofork (by simpa using hb)

end
