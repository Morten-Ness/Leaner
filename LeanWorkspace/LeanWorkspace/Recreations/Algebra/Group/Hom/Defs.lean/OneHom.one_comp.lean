import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem OneHom.one_comp [One M] [One N] [One P] (f : OneHom M N) :
    (1 : OneHom N P).comp f = 1 := rfl

