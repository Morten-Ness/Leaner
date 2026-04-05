import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem OneHom.comp_apply [One M] [One N] [One P] (g : OneHom N P) (f : OneHom M N) (x : M) :
    g.comp f x = g (f x) := rfl

