import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [HasZeroMorphisms C] [HasZeroMorphisms D]
  (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

theorem shortExact_iff_unop (S : CategoryTheory.ShortComplex Cᵒᵖ) : S.ShortExact ↔ S.unop.ShortExact := S.CategoryTheory.ShortComplex.shortExact_iff_op unop.symm

