import Mathlib

variable {M N α β : Type*}

variable [SMul M α] [SMul M β] [SMul N α] [SMul N β] (a : M) (b : α) (c : β)
  (x : α ⊕ β)

theorem smul_swap : (a • x).swap = a • x.swap := by cases x <;> rfl

