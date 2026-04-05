import Mathlib

variable (R : Type u)

theorem trop_zsmul [AddGroup R] (x : R) (n : ℤ) : Tropical.trop (n • x) = Tropical.trop x ^ n := rfl

