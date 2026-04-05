import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem fst_intCast [AddGroupWithOne R] [AddGroup M] (z : ℤ) : (z : tsze R M).fst = z := rfl

