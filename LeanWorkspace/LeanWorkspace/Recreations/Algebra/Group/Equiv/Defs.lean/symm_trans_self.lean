import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem symm_trans_self (e : M ≃* N) : e.symm.trans e = MulEquiv.refl N := DFunLike.ext _ _ MulEquiv.apply_symm_apply e

