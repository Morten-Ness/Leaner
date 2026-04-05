import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable {s : Subring R}

variable {S : Type v} [Semiring S]

theorem eqLocus_same (f : R →+* S) : f.eqLocus f = ⊤ := SetLike.ext fun _ => eq_self_iff_true _

