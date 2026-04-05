import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem snd_one [One R] [Zero M] : (1 : tsze R M).snd = 0 := rfl

