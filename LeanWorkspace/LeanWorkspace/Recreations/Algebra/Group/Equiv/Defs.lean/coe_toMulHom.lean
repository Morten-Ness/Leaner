import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem coe_toMulHom {f : M ≃* N} : (f.toMulHom : M → N) = f := rfl

