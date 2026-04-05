import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {m n : ℤ} {a b : α}

theorem zpow_right_strictMono (ha : 1 < a) : StrictMono fun n : ℤ ↦ a ^ n := by
  refine strictMono_int_of_lt_succ fun n ↦ ?_
  rw [zpow_add_one]
  exact lt_mul_of_one_lt_right' (a ^ n) ha

