import Mathlib

variable {M : Type*} [Monoid M]

theorem ofUnits_sSup (s : Set (Subgroup Mˣ)) : (sSup s).ofUnits = ⨆ S ∈ s, S.ofUnits := ofUnits_units_gc.l_sSup

