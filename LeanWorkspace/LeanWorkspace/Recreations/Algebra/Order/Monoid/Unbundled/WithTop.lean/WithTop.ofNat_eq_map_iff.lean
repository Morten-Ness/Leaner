import Mathlib

variable {α : Type u} {β : Type v}

variable [AddMonoidWithOne α]

theorem ofNat_eq_map_iff {f : β → α} {n : ℕ} [n.AtLeastTwo] {a : WithTop β} :
    ofNat(n) = a.map f ↔ ∃ x, a = .some x ∧ f x = n := some_eq_map_iff

