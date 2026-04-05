import Mathlib

variable (C : Type*) [Category* C] [Abelian C]

variable (S : SnakeInput C)

theorem L₃_exact : S.L₃.Exact := S.CategoryTheory.ShortComplex.SnakeInput.L₀_exact CategoryTheory.ShortComplex.SnakeInput.op.unop

