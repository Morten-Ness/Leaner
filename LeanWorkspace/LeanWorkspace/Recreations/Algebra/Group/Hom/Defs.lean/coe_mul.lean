import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable (M) [MulOne M]

theorem coe_mul (f g) : ((f * g : Monoid.End M) : M → M) = f ∘ g := rfl

