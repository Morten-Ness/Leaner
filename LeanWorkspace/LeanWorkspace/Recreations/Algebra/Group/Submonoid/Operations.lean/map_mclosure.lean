import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_mclosure (f : F) (s : Set M) : (closure s).map f = closure (f '' s) := Set.image_preimage.l_comm_of_u_comm (Submonoid.gc_map_comap f) (Submonoid.gi N).gc (Submonoid.gi M).gc
    fun _ ↦ rfl

