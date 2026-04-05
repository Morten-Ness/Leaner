import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Abelian C]

variable {X Y : C} (f : X ⟶ Y)

theorem cokernelSequence_exact : (CategoryTheory.ShortComplex.cokernelSequence f).Exact := CategoryTheory.ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)

