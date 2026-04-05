import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem snd_intCast [AddGroupWithOne R] [AddGroup M] (z : ℤ) : (z : tsze R M).snd = 0 := rfl

