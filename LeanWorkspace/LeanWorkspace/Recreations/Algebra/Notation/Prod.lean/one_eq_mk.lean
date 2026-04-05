import Mathlib

variable {G H M N P R S : Type*}

variable [One M] [One N]

theorem one_eq_mk : (1 : M × N) = (1, 1) := rfl

