import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem OneHom.coe_copy {_ : One M} {_ : One N} (f : OneHom M N) (f' : M → N) (h : f' = f) :
    (f.copy f' h) = f' := rfl

