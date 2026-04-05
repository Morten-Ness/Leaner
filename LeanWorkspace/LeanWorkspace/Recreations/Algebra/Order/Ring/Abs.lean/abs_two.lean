import Mathlib

variable {α : Type*}

variable [Ring α] [LinearOrder α] [IsOrderedRing α] {n : ℕ} {a b : α}

theorem abs_two : |(2 : α)| = 2 := abs_of_nonneg zero_le_two

