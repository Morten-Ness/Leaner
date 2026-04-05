import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem apply_eq_iff_eq (e : M ≃* N) {x y : M} : e x = e y ↔ x = y := MulEquiv.injective e.eq_iff

