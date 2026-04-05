import Mathlib

variable {α : Type u} {β : Type v} {R : Type x}

theorem IsUnit.sub_iff [Ring α] {x y : α} : IsUnit (x - y) ↔ IsUnit (y - x) := (IsUnit.neg_iff _).symm.trans <| neg_sub x y ▸ Iff.rfl

