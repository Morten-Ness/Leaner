import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem one_comp [MulOne M] [MulOne N] [MulOneClass P] (f : M →* N) :
    (1 : N →* P).comp f = 1 := rfl

