import Mathlib

variable {M : Type*} [Monoid M]

theorem Submonoid.ofUnits_units_le (S : Submonoid M) : S.units.ofUnits ≤ S := fun _ ⟨_, hm, he⟩ => he ▸ hm.1

