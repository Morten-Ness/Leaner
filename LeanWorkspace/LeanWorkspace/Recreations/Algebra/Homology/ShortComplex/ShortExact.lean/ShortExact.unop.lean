import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [HasZeroMorphisms C] [HasZeroMorphisms D]
  (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

theorem ShortExact.unop {S : CategoryTheory.ShortComplex Cᵒᵖ} (h : S.ShortExact) : S.unop.ShortExact where
  exact := h.exact.unop
  mono_f := by
    have := h.epi_g
    dsimp
    infer_instance
  epi_g := by
    have := h.mono_f
    dsimp
    infer_instance

