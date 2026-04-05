import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [LocallyFiniteOrder α]

variable [Add α] [SuccAddOrder α] {a b : α}

theorem insert_Ioc_add_one_left_eq_Ioc (h : a < b) : insert (a + 1) (Ioc (a + 1) b) = Ioc a b := by
  simpa [succ_eq_add_one] using insert_Ioc_succ_left_eq_Ioc h

