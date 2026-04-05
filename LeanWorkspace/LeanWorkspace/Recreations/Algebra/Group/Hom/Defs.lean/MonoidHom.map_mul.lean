import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MonoidHom.map_mul [MulOne M] [MulOne N] (f : M →* N) (a b : M) :
    f (a * b) = f a * f b := f.map_mul' a b

