import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem map_mul (f : M ≃* N) : ∀ x y, f (x * y) = f x * f y := map_mul f

