import Mathlib

variable {α β : Type*}

variable [LinearOrderedCommGroupWithZero α] {a b c d : α} {m n : ℕ}

theorem denselyOrdered_units_iff [Nontrivial αˣ] : DenselyOrdered αˣ ↔ DenselyOrdered α := by
  have := denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units (α := α)
  tauto

