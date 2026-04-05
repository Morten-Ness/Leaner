import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MonoidHom.one_apply [MulOne M] [MulOneClass N] (x : M) : (1 : M →* N) x = 1 := rfl

