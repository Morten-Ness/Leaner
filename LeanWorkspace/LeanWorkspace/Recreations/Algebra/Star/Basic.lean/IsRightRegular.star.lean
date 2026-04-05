import Mathlib

open scoped Ring

variable {R : Type u}

theorem IsRightRegular.star [Mul R] [StarMul R] {x : R} (hx : IsRightRegular x) :
    IsLeftRegular (star x) := fun a b h => star_injective <| hx <| by simpa using congr_arg Star.star h

