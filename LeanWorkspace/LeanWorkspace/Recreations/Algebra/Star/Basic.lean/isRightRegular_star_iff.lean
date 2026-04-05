import Mathlib

open scoped Ring

variable {R : Type u}

theorem isRightRegular_star_iff [Mul R] [StarMul R] {x : R} :
    IsRightRegular (star x) ↔ IsLeftRegular x := ⟨fun h => star_star x ▸ h.star, (·.star)⟩

