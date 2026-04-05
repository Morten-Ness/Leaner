import Mathlib

variable {α : Type u} {β : Type v}

variable [AddMonoidWithOne α]

theorem map_eq_ofNat_iff {f : β → α} {n : ℕ} [n.AtLeastTwo] {a : WithBot β} :
    a.map f = ofNat(n) ↔ ∃ x, a = .some x ∧ f x = n := map_eq_some_iff

