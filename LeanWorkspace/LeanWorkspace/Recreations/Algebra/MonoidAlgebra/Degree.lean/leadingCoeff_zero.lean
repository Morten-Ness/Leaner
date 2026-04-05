import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

theorem leadingCoeff_zero [Nonempty A] : (0 : R[A]).leadingCoeff D = 0 := rfl

