import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem snd_zero [Zero R] [Zero M] : (0 : tsze R M).snd = 0 := rfl

