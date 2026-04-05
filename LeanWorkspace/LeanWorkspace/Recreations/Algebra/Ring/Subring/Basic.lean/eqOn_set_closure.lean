import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable {s : Subring R}

variable {S : Type v} [Semiring S]

theorem eqOn_set_closure {f g : R →+* S} {s : Set R} (h : Set.EqOn f g s) :
    Set.EqOn f g (Subring.closure s) := show Subring.closure s ≤ f.eqLocus g from Subring.closure_le.2 h

