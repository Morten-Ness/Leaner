import Mathlib

variable {A M G α β γ : Type*}

theorem trans_one {α : Sort*} {β : Type*} (e : α ≃ β) : e.trans (1 : Equiv.Perm β) = e := Equiv.trans_refl e

