import Mathlib

variable {A M G α β γ : Type*}

theorem _root_.Equiv.permCongrHom_trans (e : α ≃ β) (e' : β ≃ γ) :
    e.permCongrHom.trans e'.permCongrHom = (e.trans e').permCongrHom := rfl

