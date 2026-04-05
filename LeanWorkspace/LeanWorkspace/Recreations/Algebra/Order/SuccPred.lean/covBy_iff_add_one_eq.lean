import Mathlib

variable {α : Type*} {x y : α}

variable [PartialOrder α]

theorem covBy_iff_add_one_eq [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] :
    x ⋖ y ↔ x + 1 = y := by
  rw [← Order.succ_eq_add_one]
  exact succ_eq_iff_covBy.symm

