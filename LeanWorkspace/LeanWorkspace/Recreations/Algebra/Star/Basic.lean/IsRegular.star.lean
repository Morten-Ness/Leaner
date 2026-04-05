import Mathlib

open scoped Ring

variable {R : Type u}

theorem IsRegular.star [Mul R] [StarMul R] {x : R} (hx : IsRegular x) :
    IsRegular (star x) := ⟨hx.right.star, hx.left.star⟩

