import Mathlib

open scoped Ring

variable {R : Type u}

theorem isLeftRegular_star_iff [Mul R] [StarMul R] {x : R} :
    IsLeftRegular (star x) ↔ IsRightRegular x := ⟨fun h => star_star x ▸ h.star, (·.star)⟩

