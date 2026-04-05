import Mathlib

variable {α : Type u} {β : Type v}

variable [AddMonoidWithOne α]

theorem map_eq_natCast_iff {f : β → α} {n : ℕ} {a : WithBot β} :
    a.map f = n ↔ ∃ x, a = .some x ∧ f x = n := map_eq_some_iff

