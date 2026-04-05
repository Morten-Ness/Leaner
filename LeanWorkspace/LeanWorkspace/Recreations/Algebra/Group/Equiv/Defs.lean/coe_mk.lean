import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem coe_mk (f : M ≃ N) (hf : ∀ x y, f (x * y) = f x * f y) : (MulEquiv.mk f hf : M → N) = f := rfl

