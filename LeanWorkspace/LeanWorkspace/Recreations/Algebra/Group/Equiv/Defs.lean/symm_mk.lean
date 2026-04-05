import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem symm_mk (f : M ≃ N) (h) :
    (MulEquiv.mk f h).symm = ⟨f.symm, MulEquiv.symm_map_mul (MulEquiv.mk f h)⟩ := rfl

