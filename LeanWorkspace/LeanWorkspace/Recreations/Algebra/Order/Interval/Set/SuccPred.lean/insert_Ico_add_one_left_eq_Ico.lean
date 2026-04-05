import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [Add α] [SuccAddOrder α] {a b : α}

theorem insert_Ico_add_one_left_eq_Ico (h : a < b) : insert a (Ico (a + 1) b) = Ico a b := by
  simpa [succ_eq_add_one] using insert_Ico_succ_left_eq_Ico h

