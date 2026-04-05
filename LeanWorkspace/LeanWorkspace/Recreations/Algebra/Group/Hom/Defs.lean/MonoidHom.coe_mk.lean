import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MonoidHom.coe_mk [MulOne M] [MulOne N] (f hmul) :
    (MonoidHom.mk f hmul : M → N) = f := rfl

