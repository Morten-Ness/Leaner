import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [Add α] [SuccAddOrder α] {a b : α}

theorem insert_Icc_add_one_left_eq_Icc (h : a ≤ b) : insert a (Icc (a + 1) b) = Icc a b := by
  simpa [succ_eq_add_one] using insert_Icc_succ_left_eq_Icc h

