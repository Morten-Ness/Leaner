import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable (h : S.LeftHomologyData) {A : C}

theorem liftK_i (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : h.liftK k hk ≫ h.i = k := h.hi.fac _ WalkingParallelPair.zero

