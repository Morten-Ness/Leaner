import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem inl_injective [Zero M] : Function.Injective (TrivSqZeroExt.inl : R → tsze R M) := Function.LeftInverse.injective <| TrivSqZeroExt.fst_inl _

