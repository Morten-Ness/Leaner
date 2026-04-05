import Mathlib

variable {M : Type*} [Monoid M]

theorem ofUnits_le_iff_le_units (S : Submonoid M) (H : Subgroup Mˣ) :
    H.ofUnits ≤ S ↔ H ≤ S.units := ofUnits_units_gc _ _

