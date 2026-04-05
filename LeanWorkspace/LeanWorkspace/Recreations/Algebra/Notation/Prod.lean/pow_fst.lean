import Mathlib

variable {G H M N P R S : Type*}

variable {E α β : Type*} [Pow α E] [Pow β E]

theorem pow_fst (p : α × β) (c : E) : (p ^ c).fst = p.fst ^ c := rfl

