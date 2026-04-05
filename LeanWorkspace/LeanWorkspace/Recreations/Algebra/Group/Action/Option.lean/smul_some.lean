import Mathlib

variable {M N α : Type*}

variable [SMul M α] [SMul N α] (a : M) (b : α) (x : Option α)

theorem smul_some : a • some b = some (a • b) := rfl

