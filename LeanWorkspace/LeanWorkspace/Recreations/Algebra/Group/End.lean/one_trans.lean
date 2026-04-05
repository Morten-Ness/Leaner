import Mathlib

variable {A M G α β γ : Type*}

theorem one_trans {α : Type*} {β : Sort*} (e : α ≃ β) : (1 : Equiv.Perm α).trans e = e := rfl

