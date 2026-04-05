import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem self_trans_symm (e : M ≃* N) : e.trans e.symm = MulEquiv.refl M := DFunLike.ext _ _ MulEquiv.symm_apply_apply e

