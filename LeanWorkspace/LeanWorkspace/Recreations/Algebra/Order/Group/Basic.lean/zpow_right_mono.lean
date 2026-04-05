import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {m n : ℤ} {a b : α}

theorem zpow_right_mono (ha : 1 ≤ a) : Monotone fun n : ℤ ↦ a ^ n := by
  refine monotone_int_of_le_succ fun n ↦ ?_
  rw [zpow_add_one]
  exact le_mul_of_one_le_right' ha

