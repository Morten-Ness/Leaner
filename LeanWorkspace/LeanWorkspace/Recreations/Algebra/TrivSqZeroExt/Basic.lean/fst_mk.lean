import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem fst_mk (r : R) (m : M) : TrivSqZeroExt.fst (r, m) = r := rfl

