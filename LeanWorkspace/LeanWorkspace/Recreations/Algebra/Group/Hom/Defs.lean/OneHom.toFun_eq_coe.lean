import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem OneHom.toFun_eq_coe [One M] [One N] (f : OneHom M N) : f.toFun = f := rfl

