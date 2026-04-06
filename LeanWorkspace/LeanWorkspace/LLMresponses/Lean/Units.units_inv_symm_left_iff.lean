import Mathlib

open scoped Int

variable {M : Type*}

variable [Monoid M]

theorem units_inv_symm_left_iff {a : Mˣ} {x y : M} : SemiconjBy (↑a⁻¹) y x ↔ SemiconjBy (↑a) x y := by
  simpa using a.inv_symm_left_iff (a := x) (b := y)
