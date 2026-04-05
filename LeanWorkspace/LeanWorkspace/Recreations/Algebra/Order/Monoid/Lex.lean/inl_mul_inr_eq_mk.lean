import Mathlib

variable (α β : Type*) [Monoid α] [PartialOrder α] [Monoid β] [Preorder β]

theorem inl_mul_inr_eq_mk (m : α) (n : β) : OrderMonoidHom.inl α β m * OrderMonoidHom.inr α β n = (m, n) := by
  simp

