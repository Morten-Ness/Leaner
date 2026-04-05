import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_mul' [CommMagma R] [StarMul R] (x y : R) : star (x * y) = star x * star y := (star_mul x y).trans (mul_comm _ _)

