import Mathlib

variable {G H M N P R S : Type*}

variable {E α β : Type*} [Pow α E] [Pow β E]

theorem pow_snd (p : α × β) (c : E) : (p ^ c).snd = p.snd ^ c := rfl

