import Mathlib

theorem free_map_coe {α β : Type u} {f : α → β} : ⇑(CommRingCat.free.map f) = ⇑(rename f) := rfl

