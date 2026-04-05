import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [Add α] [SuccAddOrder α] {a b : α}

theorem insert_Ioc_right_eq_Ioc_add_one_of_not_isMax (h : a ≤ b) (hb : ¬ IsMax b) :
    insert (b + 1) (Ioc a b) = Ioc a (b + 1) := by
  simpa [succ_eq_add_one] using insert_Ioc_right_eq_Ioc_succ_of_not_isMax h hb

