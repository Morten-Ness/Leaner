import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Abelian C]

variable {X Y : C} (f : X ⟶ Y)

theorem kernelSequence_exact : (CategoryTheory.ShortComplex.kernelSequence f).Exact := CategoryTheory.ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f)

