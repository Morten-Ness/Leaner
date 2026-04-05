import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

variable {H K : Subgroup G}

theorem subgroupMap_symm_apply (e : G ≃* G') (H : Subgroup G) (g : H.map (e : G →* G')) :
    (e.subgroupMap H).symm g = ⟨e.symm g, SetLike.mem_coe.1 <| Set.mem_image_equiv.1 g.2⟩ := rfl

