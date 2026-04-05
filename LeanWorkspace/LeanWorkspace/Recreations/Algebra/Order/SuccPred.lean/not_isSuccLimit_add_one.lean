import Mathlib

variable {α : Type*} {x y : α}

variable [PartialOrder α]

theorem not_isSuccLimit_add_one (a : α) [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] :
    ¬ IsSuccLimit (a + 1) := Order.succ_eq_add_one a ▸ not_isSuccLimit_succ a

