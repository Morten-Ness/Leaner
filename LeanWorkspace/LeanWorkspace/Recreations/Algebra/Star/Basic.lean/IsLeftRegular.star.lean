import Mathlib

open scoped Ring

variable {R : Type u}

theorem IsLeftRegular.star [Mul R] [StarMul R] {x : R} (hx : IsLeftRegular x) :
    IsRightRegular (star x) := fun a b h => star_injective <| hx <| by simpa using congr_arg Star.star h

