import Mathlib

variable {R A : Type*}

theorem snd_one [One R] [Zero A] : (1 : Unitization R A).snd = 0 := rfl

