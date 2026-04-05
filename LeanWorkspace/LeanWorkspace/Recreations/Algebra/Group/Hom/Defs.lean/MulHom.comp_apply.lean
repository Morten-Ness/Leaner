import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MulHom.comp_apply [Mul M] [Mul N] [Mul P] (g : N →ₙ* P) (f : M →ₙ* N) (x : M) :
    g.comp f x = g (f x) := rfl

