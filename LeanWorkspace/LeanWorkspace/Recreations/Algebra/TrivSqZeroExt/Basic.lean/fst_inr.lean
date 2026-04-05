import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem fst_inr [Zero R] (m : M) : (TrivSqZeroExt.inr m : tsze R M).fst = 0 := rfl

