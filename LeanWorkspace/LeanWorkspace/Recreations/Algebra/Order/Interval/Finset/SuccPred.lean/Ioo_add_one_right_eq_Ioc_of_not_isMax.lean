import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [LocallyFiniteOrder α]

variable [Add α] [SuccAddOrder α] {a b : α}

theorem Ioo_add_one_right_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ioo a (b + 1) = Ioc a b := by
  simpa [succ_eq_add_one] using Ioo_succ_right_eq_Ioc_of_not_isMax hb a

