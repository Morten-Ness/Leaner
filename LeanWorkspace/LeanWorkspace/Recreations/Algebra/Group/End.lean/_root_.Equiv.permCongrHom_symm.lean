import Mathlib

variable {A M G α β γ : Type*}

theorem _root_.Equiv.permCongrHom_symm (e : α ≃ β) :
    e.permCongrHom.symm = e.symm.permCongrHom := rfl

