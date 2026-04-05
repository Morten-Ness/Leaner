import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [LocallyFiniteOrder α]

variable [Add α] [SuccAddOrder α] {a b : α}

variable [NoMaxOrder α]

theorem insert_Ico_right_eq_Ico_add_one (h : a ≤ b) : insert b (Ico a b) = Ico a (b + 1) := by
  simpa [succ_eq_add_one] using insert_Ico_right_eq_Ico_succ h

