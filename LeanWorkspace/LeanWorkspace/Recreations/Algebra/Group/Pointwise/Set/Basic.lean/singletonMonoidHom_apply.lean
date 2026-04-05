import Mathlib

variable {F α β γ : Type*}

variable [MulOneClass α]

theorem singletonMonoidHom_apply (a : α) : Set.singletonMonoidHom a = {a} := rfl

