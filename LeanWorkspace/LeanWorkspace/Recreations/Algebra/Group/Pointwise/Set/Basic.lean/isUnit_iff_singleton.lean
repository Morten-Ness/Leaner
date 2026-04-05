import Mathlib

variable {F α β γ : Type*}

variable [Group α] {s t : Set α} {a b : α}

theorem isUnit_iff_singleton : IsUnit s ↔ ∃ a, s = {a} := by
  simp only [Set.isUnit_iff, Group.isUnit, and_true]

