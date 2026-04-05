import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem fst_inl [Zero M] (r : R) : (TrivSqZeroExt.inl r : tsze R M).fst = r := rfl

