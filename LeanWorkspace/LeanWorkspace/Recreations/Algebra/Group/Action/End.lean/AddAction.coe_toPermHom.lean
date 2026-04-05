import Mathlib

variable {G M N A α : Type*}

variable (G α) [AddGroup G] [AddAction G α]

theorem AddAction.coe_toPermHom :
    ⇑(AddAction.toPermHom G α) = AddAction.toPerm := rfl

