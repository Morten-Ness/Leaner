import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable {s : Subsemiring R}

variable {σR σS : Type*}

variable [SetLike σR R] [SetLike σS S] [SubsemiringClass σR R] [SubsemiringClass σS S]

theorem map_closureS (f : R →+* S) (s : Set R) : (Subsemiring.closure s).map f = Subsemiring.closure (f '' s) := Set.image_preimage.l_comm_of_u_comm (Subsemiring.gc_map_comap f) (Subsemiring.gi S).gc (Subsemiring.gi R).gc
    fun _ ↦ coe_comap _ _

