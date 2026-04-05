import Mathlib

variable {α β G M : Type*}

variable [CommMonoid M] {x y z : M}

theorem inv_unique (hy : x * y = 1) (hz : x * z = 1) : y = z := left_inv_eq_right_inv (Trans.trans (mul_comm _ _) hy) hz

