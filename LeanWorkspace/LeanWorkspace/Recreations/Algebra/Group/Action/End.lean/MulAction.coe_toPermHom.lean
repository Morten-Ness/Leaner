import Mathlib

variable {G M N A α : Type*}

variable (G α) [Group G] [MulAction G α]

theorem MulAction.coe_toPermHom :
    ⇑(MulAction.toPermHom G α) = MulAction.toPerm := rfl

