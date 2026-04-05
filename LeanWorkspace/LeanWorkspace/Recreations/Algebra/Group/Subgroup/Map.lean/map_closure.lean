import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem map_closure (f : G →* N) (s : Set G) : (closure s).map f = closure (f '' s) := Set.image_preimage.l_comm_of_u_comm (Subgroup.gc_map_comap f) (Subgroup.gi N).gc (Subgroup.gi G).gc
    fun _ ↦ rfl

