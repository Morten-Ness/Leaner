import Mathlib

variable {R A : Type*}

theorem star_comm_self' [Mul R] [Star R] (x : R) [IsStarNormal x] : star x * x = x * star x := IsStarNormal.star_comm_self

