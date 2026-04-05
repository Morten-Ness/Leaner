import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MonoidHom.toMulHom_coe [MulOne M] [MulOne N] (f : M →* N) :
    f.toMulHom.toFun = f := rfl

