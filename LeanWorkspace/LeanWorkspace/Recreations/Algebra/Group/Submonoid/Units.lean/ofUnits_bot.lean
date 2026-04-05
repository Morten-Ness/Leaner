import Mathlib

variable {M : Type*} [Monoid M]

theorem ofUnits_bot : (⊥ : Subgroup Mˣ).ofUnits = ⊥ := ofUnits_units_gc.l_bot

