import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Subfield K}

theorem map_field_closure (f : K →+* L) (s : Set K) : (Subfield.closure s).map f = Subfield.closure (f '' s) := Set.image_preimage.l_comm_of_u_comm (Subfield.gc_map_comap f) (Subfield.gi L).gc (Subfield.gi K).gc
    fun _ ↦ rfl

