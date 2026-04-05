import Mathlib

variable (α β : Type*) [Monoid α] [PartialOrder α] [Monoid β] [Preorder β]

theorem inlₗ_mul_inrₗ_eq_toLex (m : α) (n : β) : OrderMonoidHom.inlₗ α β m * OrderMonoidHom.inrₗ α β n = toLex (m, n) := by
  simp [← toLex_mul]

