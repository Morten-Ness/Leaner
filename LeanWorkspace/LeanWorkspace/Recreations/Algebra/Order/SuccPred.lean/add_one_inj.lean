import Mathlib

variable {α : Type*} {x y : α}

variable [LinearOrder α]

variable [Add α] [One α] [SuccAddOrder α]

theorem add_one_inj [NoMaxOrder α] : x + 1 = y + 1 ↔ x = y := by
  simp [← Order.succ_eq_add_one]

