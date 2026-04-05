import Mathlib

variable (C : Type*) [Category* C] [Abelian C]

variable (S : SnakeInput C)

theorem L₂'_exact : S.L₂'.Exact := by
  rw [← exact_op_iff, exact_iff_of_iso S.L₂'OpIso]
  exact S.CategoryTheory.ShortComplex.SnakeInput.L₁'_exact CategoryTheory.ShortComplex.SnakeInput.op

