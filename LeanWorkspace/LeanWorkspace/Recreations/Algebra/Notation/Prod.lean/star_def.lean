import Mathlib

variable {G H M N P R S : Type*}

variable [Star R] [Star S]

theorem star_def (x : R × S) : star x = (star x.1, star x.2) := rfl

