import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MonoidHom.toOneHom_coe [MulOne M] [MulOne N] (f : M →* N) :
    (f.toOneHom : M → N) = f := rfl

