import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [LocallyFiniteOrder α]

variable [Add α] [SuccAddOrder α] {a b : α}

theorem Ico_add_one_add_one_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) :
    Ico (a + 1) (b + 1) = Ioc a b := by
  simpa [succ_eq_add_one] using Ico_succ_succ_eq_Ioc_of_not_isMax hb a

