import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

variable {H K : Subgroup G}

theorem coe_subgroupMap_apply (e : G ≃* G') (H : Subgroup G) (g : H) :
    ((MulEquiv.subgroupMap e H g : H.map (e : G →* G')) : G') = e g := rfl

