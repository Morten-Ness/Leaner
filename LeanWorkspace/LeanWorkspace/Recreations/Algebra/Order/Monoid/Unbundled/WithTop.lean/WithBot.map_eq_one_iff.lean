import Mathlib

variable {α : Type u} {β : Type v}

variable [One α] {a : α}

theorem map_eq_one_iff {α} {f : α → β} {v : WithBot α} [One β] :
    WithBot.map f v = 1 ↔ ∃ x, v = .some x ∧ f x = 1 := map_eq_some_iff

