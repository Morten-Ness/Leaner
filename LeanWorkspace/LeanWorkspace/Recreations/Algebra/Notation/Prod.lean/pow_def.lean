import Mathlib

variable {G H M N P R S : Type*}

variable {E α β : Type*} [Pow α E] [Pow β E]

theorem pow_def (p : α × β) (c : E) : p ^ c = (p.1 ^ c, p.2 ^ c) := rfl

