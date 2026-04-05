import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable {s : Subring R}

theorem map_closure (f : R →+* S) (s : Set R) : (Subring.closure s).map f = Subring.closure (f '' s) := Set.image_preimage.l_comm_of_u_comm (Subring.gc_map_comap f) (Subring.gi S).gc (Subring.gi R).gc
    fun _ ↦ rfl

