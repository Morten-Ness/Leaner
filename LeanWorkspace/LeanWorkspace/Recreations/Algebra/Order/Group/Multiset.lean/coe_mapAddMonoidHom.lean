import Mathlib

variable {α β : Type*}

theorem coe_mapAddMonoidHom (f : α → β) : (Multiset.mapAddMonoidHom f : Multiset α → Multiset β) = map f := rfl

