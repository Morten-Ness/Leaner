import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem hasCokernel [S.HasRightHomology] : HasCokernel S.f := ⟨⟨⟨_, S.rightHomologyData.hp⟩⟩⟩

