import Mathlib

variable {α : Type*}

variable [One α] {p : Prop} [Decidable p] {a : p → α} {b : ¬p → α}

theorem dite_lt_one [LT α] (ha : ∀ h, a h < 1) (hb : ∀ h, b h < 1) : dite p a b < 1 := by
  split; exacts [ha ‹_›, hb ‹_›]

