import Mathlib

variable (R : Type u)

theorem trop_nsmul [AddMonoid R] (x : R) (n : ℕ) : Tropical.trop (n • x) = Tropical.trop x ^ n := rfl

