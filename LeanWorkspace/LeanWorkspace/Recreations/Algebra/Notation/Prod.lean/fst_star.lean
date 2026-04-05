import Mathlib

variable {G H M N P R S : Type*}

variable [Star R] [Star S]

theorem fst_star (x : R × S) : (star x).1 = star x.1 := rfl

