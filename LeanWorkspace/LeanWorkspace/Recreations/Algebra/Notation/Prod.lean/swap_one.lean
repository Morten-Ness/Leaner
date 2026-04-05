import Mathlib

variable {G H M N P R S : Type*}

variable [One M] [One N]

theorem swap_one : (1 : M × N).swap = 1 := rfl

