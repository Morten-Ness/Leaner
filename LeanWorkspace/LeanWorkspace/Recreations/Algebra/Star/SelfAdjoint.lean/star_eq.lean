import Mathlib

variable {R A : Type*}

theorem star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) : star x = x := hx

grind_pattern star_eq => IsSelfAdjoint x, star x

