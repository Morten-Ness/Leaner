import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [LocallyFiniteOrder α]

variable [Add α] [SuccAddOrder α] {a b : α}

theorem Ico_add_one_right_eq_Icc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ico a (b + 1) = Icc a b := by
  simpa [succ_eq_add_one] using Ico_succ_right_eq_Icc_of_not_isMax hb a

