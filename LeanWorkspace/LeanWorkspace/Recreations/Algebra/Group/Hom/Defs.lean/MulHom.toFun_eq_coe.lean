import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MulHom.toFun_eq_coe [Mul M] [Mul N] (f : M →ₙ* N) : f.toFun = f := rfl

