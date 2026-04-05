import Mathlib

variable {M : Type*}

theorem Irreducible.associated_of_dvd [Monoid M] {p q : M} (p_irr : Irreducible p)
    (q_irr : Irreducible q) (dvd : p ∣ q) : Associated p q := ((q_irr.dvd_iff.mp dvd).resolve_left p_irr.not_isUnit).symm

