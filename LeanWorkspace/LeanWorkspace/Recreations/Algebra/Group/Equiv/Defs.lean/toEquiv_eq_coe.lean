import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem toEquiv_eq_coe (f : M ≃* N) : f.toEquiv = f := rfl

