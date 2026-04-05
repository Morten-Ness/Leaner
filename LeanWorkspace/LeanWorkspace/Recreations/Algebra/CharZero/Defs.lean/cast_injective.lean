import Mathlib

variable {R : Type*}

variable [AddMonoidWithOne R] [CharZero R]

theorem cast_injective : Function.Injective (Nat.cast : ℕ → R) := CharZero.cast_injective

