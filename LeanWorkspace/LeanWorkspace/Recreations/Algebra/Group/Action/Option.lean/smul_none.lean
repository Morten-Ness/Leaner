import Mathlib

variable {M N α : Type*}

variable [SMul M α] [SMul N α] (a : M) (b : α) (x : Option α)

theorem smul_none : a • (none : Option α) = none := rfl

