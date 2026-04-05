import Mathlib

variable {α : Type*} {x y : α}

variable [PartialOrder α]

theorem IsSuccPrelimit.add_one_lt [Add α] [One α] [SuccAddOrder α]
    (hx : IsSuccPrelimit x) (hy : y < x) : y + 1 < x := by
  rw [← Order.succ_eq_add_one]
  exact hx.succ_lt hy

