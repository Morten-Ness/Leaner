import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem subgroupOf_map_subtype (H K : Subgroup G) : (H.subgroupOf K).map K.subtype = H ⊓ K := SetLike.ext' <| by refine Subtype.image_preimage_coe _ _ |>.trans ?_; apply Set.inter_comm

