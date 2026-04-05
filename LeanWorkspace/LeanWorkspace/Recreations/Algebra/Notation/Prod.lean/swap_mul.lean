import Mathlib

variable {G H M N P R S : Type*}

variable {M N : Type*} [Mul M] [Mul N]

theorem swap_mul (p q : M × N) : (p * q).swap = p.swap * q.swap := rfl

