import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem isUnit_iff_eq_one (a : Associates M) : IsUnit a ↔ a = 1 := Iff.intro (fun ⟨_, h⟩ => h ▸ Associates.coe_unit_eq_one _) fun h => Associated.symm h ▸ isUnit_one

