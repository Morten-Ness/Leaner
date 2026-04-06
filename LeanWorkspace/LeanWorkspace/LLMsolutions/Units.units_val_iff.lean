import Mathlib

open scoped Int

variable {M : Type*}

variable [Monoid M]

theorem units_val_iff {a x y : Mˣ} : SemiconjBy (a : M) x y ↔ SemiconjBy a x y := by
  change ((a : M) * (x : M) = (y : M) * (a : M)) ↔ ((a * x : Mˣ) = y * a)
  simp [SemiconjBy, Units.ext_iff]
