import Mathlib

variable {α : Type u} {β : Type v}

variable [One α] {a : α}

theorem one_eq_map_iff {α} {f : α → β} {v : WithTop α} [One β] :
    1 = WithTop.map f v ↔ ∃ x, v = .some x ∧ f x = 1 := some_eq_map_iff

