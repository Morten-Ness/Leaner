import Mathlib

variable {F α β R S S' : Type*}

theorem noZeroDivisors {A : Type*} (B : Type*) [MulZeroClass A] [MulZeroClass B]
    [NoZeroDivisors B] (e : A ≃* B) : NoZeroDivisors A := RingEquiv.injective e.noZeroDivisors e (RingEquiv.map_zero e) (RingEquiv.map_mul e)

