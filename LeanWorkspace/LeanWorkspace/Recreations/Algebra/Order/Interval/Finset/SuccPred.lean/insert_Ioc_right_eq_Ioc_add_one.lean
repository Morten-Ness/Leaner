import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [LocallyFiniteOrder α]

variable [Add α] [SuccAddOrder α] {a b : α}

variable [NoMaxOrder α]

theorem insert_Ioc_right_eq_Ioc_add_one (h : a ≤ b) : insert (b + 1) (Ioc a b) = Ioc a (b + 1) := Finset.insert_Ioc_right_eq_Ioc_add_one_of_not_isMax h (not_isMax _)

