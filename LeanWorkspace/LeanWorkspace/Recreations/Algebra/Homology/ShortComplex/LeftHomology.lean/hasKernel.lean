import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

theorem hasKernel [S.HasLeftHomology] : HasKernel S.g := ⟨⟨⟨_, S.leftHomologyData.hi⟩⟩⟩

