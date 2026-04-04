import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

theorem finite_set_of_fin_dim_affineIndependent [FiniteDimensional k V] {s : Set ι} {f : s → P}
    (hi : AffineIndependent k f) : s.Finite := @Set.toFinite _ s (finite_of_fin_dim_affineIndependent k hi)

