import Mathlib

open scoped Int

variable {M : Type*}

variable [Monoid M]

theorem units_val_iff {a x y : Mˣ} : SemiconjBy (a : M) x y ↔ SemiconjBy a x y := ⟨SemiconjBy.units_of_val, SemiconjBy.units_val⟩

