import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [Add α] [SuccAddOrder α] {a b : α}

theorem insert_Ico_right_eq_Ico_add_one_of_not_isMax (h : a ≤ b) (hb : ¬ IsMax b) :
    insert b (Ico a b) = Ico a (b + 1) := by
  simpa [succ_eq_add_one] using insert_Ico_right_eq_Ico_succ_of_not_isMax h hb

