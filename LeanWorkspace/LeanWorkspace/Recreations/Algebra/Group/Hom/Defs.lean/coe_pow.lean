import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable (M) [MulOne M]

theorem coe_pow (f : Monoid.End M) (n : ℕ) : (↑(f ^ n) : M → M) = f^[n] := rfl

