import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [MulOneClass α]

theorem singletonMonoidHom_apply (a : α) : Finset.singletonMonoidHom a = {a} := rfl

