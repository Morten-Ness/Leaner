import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [HasZeroMorphisms C] [HasZeroMorphisms D]
  (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

theorem shortExact_iff_op : S.ShortExact ↔ S.op.ShortExact := ⟨CategoryTheory.ShortComplex.ShortExact.op, CategoryTheory.ShortComplex.ShortExact.unop⟩

