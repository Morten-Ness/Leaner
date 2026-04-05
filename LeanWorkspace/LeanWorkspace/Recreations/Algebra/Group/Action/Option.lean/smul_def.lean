import Mathlib

variable {M N α : Type*}

variable [SMul M α] [SMul N α] (a : M) (b : α) (x : Option α)

theorem smul_def : a • x = x.map (a • ·) := rfl

