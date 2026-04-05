import Mathlib

variable {α : Type u} {β : Type v}

variable [AddMonoidWithOne α]

theorem natCast_eq_map_iff {f : β → α} {n : ℕ} {a : WithBot β} :
    n = a.map f ↔ ∃ x, a = .some x ∧ f x = n := some_eq_map_iff

