import Mathlib

variable {α : Type u} {β : Type v}

variable [One α] {a : α}

theorem one_eq_map_iff {α} {f : α → β} {v : WithBot α} [One β] :
    1 = WithBot.map f v ↔ ∃ x, v = .some x ∧ f x = 1 := some_eq_map_iff

