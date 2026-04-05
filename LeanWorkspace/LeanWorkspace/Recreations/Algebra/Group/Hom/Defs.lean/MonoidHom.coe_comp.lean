import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MonoidHom.coe_comp [MulOne M] [MulOne N] [MulOne P]
    (g : N →* P) (f : M →* N) : ↑(g.comp f) = g ∘ f := rfl

