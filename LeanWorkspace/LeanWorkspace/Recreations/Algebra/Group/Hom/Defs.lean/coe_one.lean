import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable (M) [MulOne M]

theorem coe_one : ((1 : Monoid.End M) : M → M) = id := rfl

