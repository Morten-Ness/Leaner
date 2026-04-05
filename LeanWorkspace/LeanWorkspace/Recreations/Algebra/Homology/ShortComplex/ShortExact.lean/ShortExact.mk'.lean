import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [HasZeroMorphisms C] [HasZeroMorphisms D]
  (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

theorem ShortExact.mk' (h : S.Exact) (_ : Mono S.f) (_ : Epi S.g) : S.ShortExact where
  exact := h

