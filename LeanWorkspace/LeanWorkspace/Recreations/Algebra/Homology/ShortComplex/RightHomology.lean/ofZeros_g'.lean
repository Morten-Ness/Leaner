import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable (h : S.RightHomologyData) {A : C}

theorem ofZeros_g' (hf : S.f = 0) (hg : S.g = 0) :
    (CategoryTheory.ShortComplex.RightHomologyData.ofZeros S hf hg).g' = 0 := by
  rw [← cancel_epi ((CategoryTheory.ShortComplex.RightHomologyData.ofZeros S hf hg).p), comp_zero, p_g', hg]

