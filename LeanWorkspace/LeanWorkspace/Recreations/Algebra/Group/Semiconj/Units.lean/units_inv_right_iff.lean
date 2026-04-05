import Mathlib

open scoped Int

variable {M : Type*}

variable [Monoid M]

theorem units_inv_right_iff {a : M} {x y : Mˣ} : SemiconjBy a ↑x⁻¹ ↑y⁻¹ ↔ SemiconjBy a x y := ⟨SemiconjBy.units_inv_right, SemiconjBy.units_inv_right⟩

