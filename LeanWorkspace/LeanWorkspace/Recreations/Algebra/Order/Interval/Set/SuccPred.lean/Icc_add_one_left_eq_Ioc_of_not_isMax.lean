import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [Add α] [SuccAddOrder α] {a b : α}

theorem Icc_add_one_left_eq_Ioc_of_not_isMax (ha : ¬ IsMax a) (b : α) : Icc (a + 1) b = Ioc a b := by
  simpa [succ_eq_add_one] using Icc_succ_left_eq_Ioc_of_not_isMax ha b

