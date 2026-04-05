import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [Add α] [SuccAddOrder α] {a b : α}

theorem Ico_add_one_left_eq_Ioo (a b : α) : Ico (a + 1) b = Ioo a b := by
  simpa [succ_eq_add_one] using Ico_succ_left_eq_Ioo a b

