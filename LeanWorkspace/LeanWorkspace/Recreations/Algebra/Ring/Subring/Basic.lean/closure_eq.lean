import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem closure_eq (s : Subring R) : Subring.closure (s : Set R) = s := (Subring.gi R).l_u_eq s

