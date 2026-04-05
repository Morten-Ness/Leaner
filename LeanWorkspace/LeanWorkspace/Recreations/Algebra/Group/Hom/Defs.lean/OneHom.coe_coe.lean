import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [One M] [One N]

variable [FunLike F M N]

theorem OneHom.coe_coe [OneHomClass F M N] (f : F) :
    ((f : OneHom M N) : M → N) = f := rfl

