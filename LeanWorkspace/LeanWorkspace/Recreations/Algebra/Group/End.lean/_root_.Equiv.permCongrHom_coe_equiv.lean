import Mathlib

variable {A M G α β γ : Type*}

theorem _root_.Equiv.permCongrHom_coe_equiv (e : α ≃ β) :
    (↑e.permCongrHom : Equiv.Perm α ≃ Equiv.Perm β) = e.permCongr := rfl

