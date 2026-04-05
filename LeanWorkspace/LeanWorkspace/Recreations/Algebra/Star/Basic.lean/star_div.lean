import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_div [CommGroup R] [StarMul R] (x y : R) : star (x / y) = star x / star y := map_div (starMulAut : R ≃* R) _ _

