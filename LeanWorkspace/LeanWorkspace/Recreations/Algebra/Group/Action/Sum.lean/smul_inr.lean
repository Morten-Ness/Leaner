import Mathlib

variable {M N α β : Type*}

variable [SMul M α] [SMul M β] [SMul N α] [SMul N β] (a : M) (b : α) (c : β)
  (x : α ⊕ β)

theorem smul_inr : a • (inr c : α ⊕ β) = inr (a • c) := rfl

