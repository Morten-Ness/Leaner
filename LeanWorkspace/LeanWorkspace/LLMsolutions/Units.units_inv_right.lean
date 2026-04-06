import Mathlib

open scoped Int

variable {M : Type*}

variable [Monoid M]

theorem units_inv_right {a : M} {x y : Mˣ} (h : SemiconjBy a x y) : SemiconjBy a ↑x⁻¹ ↑y⁻¹ := by
  simpa using h.units_inv_right
