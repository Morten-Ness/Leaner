import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MonoidHom.mk_coe [MulOne M] [MulOne N] (f : M →* N) (hmul) :
    MonoidHom.mk f hmul = f := MonoidHom.ext fun _ => rfl

