import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem symm_apply_eq (e : M ≃* N) {x y} : e.symm x = y ↔ x = e y := e.toEquiv.symm_apply_eq

