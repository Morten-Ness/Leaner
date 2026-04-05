import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [Mul M] [Mul N]

variable [FunLike F M N]

theorem MulHom.coe_coe [MulHomClass F M N] (f : F) : ((f : MulHom M N) : M → N) = f := rfl

