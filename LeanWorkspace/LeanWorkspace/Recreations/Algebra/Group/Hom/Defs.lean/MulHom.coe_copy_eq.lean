import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MulHom.coe_copy_eq {_ : Mul M} {_ : Mul N} (f : M →ₙ* N) (f' : M → N) (h : f' = f) :
    f.copy f' h = f := DFunLike.ext' h

