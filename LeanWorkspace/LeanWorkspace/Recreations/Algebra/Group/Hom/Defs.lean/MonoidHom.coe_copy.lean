import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MonoidHom.coe_copy {_ : MulOne M} {_ : MulOne N} (f : M →* N) (f' : M → N)
    (h : f' = f) : (f.copy f' h) = f' := rfl

