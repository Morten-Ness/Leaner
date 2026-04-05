import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem OneHom.one_apply [One M] [One N] (x : M) : (1 : OneHom M N) x = 1 := rfl

