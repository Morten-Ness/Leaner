import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem toEquiv_symm (f : M ≃* N) : (f.symm : N ≃ M) = (f : M ≃ N).symm := rfl

