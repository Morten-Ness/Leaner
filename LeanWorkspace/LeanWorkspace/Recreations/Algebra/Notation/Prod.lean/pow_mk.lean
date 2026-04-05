import Mathlib

variable {G H M N P R S : Type*}

variable {E α β : Type*} [Pow α E] [Pow β E]

theorem pow_mk (a : α) (b : β) (c : E) : Prod.mk a b ^ c = Prod.mk (a ^ c) (b ^ c) := rfl

