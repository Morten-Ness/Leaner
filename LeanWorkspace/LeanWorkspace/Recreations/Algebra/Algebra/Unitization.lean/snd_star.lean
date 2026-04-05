import Mathlib

variable {R A : Type*}

theorem snd_star [Star R] [Star A] (x : Unitization R A) : (star x).snd = star x.snd := rfl

