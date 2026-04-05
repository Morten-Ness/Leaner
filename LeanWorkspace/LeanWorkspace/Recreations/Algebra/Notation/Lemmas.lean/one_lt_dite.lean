import Mathlib

variable {α : Type*}

variable [One α] {p : Prop} [Decidable p] {a : p → α} {b : ¬p → α}

theorem one_lt_dite [LT α] (ha : ∀ h, 1 < a h) (hb : ∀ h, 1 < b h) : 1 < dite p a b := by
  split; exacts [ha ‹_›, hb ‹_›]

