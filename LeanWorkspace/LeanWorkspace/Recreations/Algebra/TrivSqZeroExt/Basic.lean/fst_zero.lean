import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem fst_zero [Zero R] [Zero M] : (0 : tsze R M).fst = 0 := rfl

