import Mathlib

variable {G H M N P R S : Type*}

variable {M N : Type*} [Mul M] [Mul N]

theorem mul_def (p q : M × N) : p * q = (p.1 * q.1, p.2 * q.2) := rfl

