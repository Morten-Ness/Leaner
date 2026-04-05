import Mathlib

variable {α : Type*} {x y : α}

variable [PartialOrder α]

theorem not_isSuccPrelimit_add_one (a : α) [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] :
    ¬ IsSuccPrelimit (a + 1) := Order.succ_eq_add_one a ▸ not_isSuccPrelimit_succ a

