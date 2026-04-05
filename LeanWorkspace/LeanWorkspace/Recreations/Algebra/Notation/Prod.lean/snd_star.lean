import Mathlib

variable {G H M N P R S : Type*}

variable [Star R] [Star S]

theorem snd_star (x : R × S) : (star x).2 = star x.2 := rfl

