import Mathlib

variable {A M G α β γ : Type*}

theorem _root_.Equiv.permCongrHom_coe (e : α ≃ β) : ⇑e.permCongrHom = ⇑e.permCongr := rfl

