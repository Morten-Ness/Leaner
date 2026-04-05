import Mathlib

variable {α β : Type*}

variable [LinearOrderedCommMonoidWithZero α] {a b : α} {n : ℕ}

theorem ne_zero_of_lt (h : b < a) : a ≠ 0 := fun h1 ↦ not_lt_zero' <| show b < 0 from h1 ▸ h

