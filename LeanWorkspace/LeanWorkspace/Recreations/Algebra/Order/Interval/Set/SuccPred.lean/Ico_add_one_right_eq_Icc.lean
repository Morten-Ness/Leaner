import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [Add α] [SuccAddOrder α] {a b : α}

variable [NoMaxOrder α]

theorem Ico_add_one_right_eq_Icc (a b : α) : Ico a (b + 1) = Icc a b := by
  simpa [succ_eq_add_one] using Ico_succ_right_eq_Icc a b

