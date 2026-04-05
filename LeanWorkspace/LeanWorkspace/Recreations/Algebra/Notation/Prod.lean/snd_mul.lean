import Mathlib

variable {G H M N P R S : Type*}

variable {M N : Type*} [Mul M] [Mul N]

theorem snd_mul (p q : M × N) : (p * q).2 = p.2 * q.2 := rfl

