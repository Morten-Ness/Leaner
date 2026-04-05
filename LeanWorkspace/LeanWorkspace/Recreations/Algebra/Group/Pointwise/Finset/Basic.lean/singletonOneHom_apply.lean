import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α] {s : Finset α} {a : α}

theorem singletonOneHom_apply (a : α) : Finset.singletonOneHom a = {a} := rfl

