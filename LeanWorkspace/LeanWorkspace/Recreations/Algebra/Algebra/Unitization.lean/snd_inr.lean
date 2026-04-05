import Mathlib

variable {R A : Type*}

theorem snd_inr [Zero R] (a : A) : (a : Unitization R A).snd = a := rfl

