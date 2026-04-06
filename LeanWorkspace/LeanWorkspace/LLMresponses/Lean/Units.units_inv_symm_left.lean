FAIL
import Mathlib

open scoped Int

variable {M : Type*}

variable [Monoid M]

theorem units_inv_symm_left {a : Mˣ} {x y : M} (h : SemiconjBy (↑a) x y) : SemiconjBy (↑a⁻¹) y x := by
  simpa using h.units_inv_symm_left a
