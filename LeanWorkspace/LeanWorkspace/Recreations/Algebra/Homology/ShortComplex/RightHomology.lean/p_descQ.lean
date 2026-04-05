import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable (h : S.RightHomologyData) {A : C}

theorem p_descQ (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) : h.p ≫ h.descQ k hk = k := h.hp.fac _ WalkingParallelPair.one

