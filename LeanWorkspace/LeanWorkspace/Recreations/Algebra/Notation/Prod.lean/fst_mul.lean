import Mathlib

variable {G H M N P R S : Type*}

variable {M N : Type*} [Mul M] [Mul N]

theorem fst_mul (p q : M × N) : (p * q).1 = p.1 * q.1 := rfl

