import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MonoidHom.comp_assoc {Q : Type*} [MulOne M] [MulOne N] [MulOne P]
    [MulOne Q] (f : M →* N) (g : N →* P) (h : P →* Q) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

