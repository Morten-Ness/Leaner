import Mathlib

variable {M N α β : Type*}

variable [SMul M α] [SMul M β] [SMul N α] [SMul N β] (a : M) (b : α) (c : β)
  (x : α ⊕ β)

theorem smul_inl : a • (inl b : α ⊕ β) = inl (a • b) := rfl

