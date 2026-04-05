import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

theorem exact_op_iff : S.op.Exact ↔ S.Exact := ⟨CategoryTheory.ShortComplex.Exact.unop, CategoryTheory.ShortComplex.Exact.op⟩

