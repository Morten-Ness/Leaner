import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

theorem exact_unop_iff (S : CategoryTheory.ShortComplex Cᵒᵖ) : S.unop.Exact ↔ S.Exact := S.CategoryTheory.ShortComplex.exact_op_iff unop.symm

