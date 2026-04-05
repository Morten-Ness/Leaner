import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem fst_one [One R] [Zero M] : (1 : tsze R M).fst = 1 := rfl

