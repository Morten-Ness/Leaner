import Mathlib

open scoped Int

variable {M : Type*}

variable [Monoid M]

theorem units_inv_right_iff {a : M} {x y : Mˣ} : SemiconjBy a ↑x⁻¹ ↑y⁻¹ ↔ SemiconjBy a x y := by
  simpa using x.semiconjBy_right_iff_inv_right (a := a) (c := y)
