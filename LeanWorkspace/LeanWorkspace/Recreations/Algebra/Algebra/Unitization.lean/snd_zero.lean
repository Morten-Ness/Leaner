import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem snd_zero [Zero R] [Zero A] : (0 : Unitization R A).snd = 0 := rfl

