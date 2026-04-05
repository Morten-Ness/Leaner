import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable {s : Subring R}

variable {S : Type v} [Semiring S]

theorem eq_of_eqOn_set_dense {s : Set R} (hs : Subring.closure s = ⊤) {f g : R →+* S} (h : s.EqOn f g) :
    f = g := RingHom.eq_of_eqOn_set_top <| hs ▸ RingHom.eqOn_set_closure h

