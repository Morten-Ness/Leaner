import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MonoidHom.comp_apply [MulOne M] [MulOne N] [MulOne P]
    (g : N →* P) (f : M →* N) (x : M) : g.comp f x = g (f x) := rfl

