import Mathlib

open scoped Ring

variable {R : Type u}

theorem isUnit_star [Monoid R] [StarMul R] {a : R} : IsUnit (star a) ↔ IsUnit a := ⟨fun h => star_star a ▸ h.star, IsUnit.star⟩

