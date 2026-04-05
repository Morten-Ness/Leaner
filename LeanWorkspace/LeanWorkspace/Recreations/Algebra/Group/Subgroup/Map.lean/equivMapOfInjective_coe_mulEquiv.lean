import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem equivMapOfInjective_coe_mulEquiv (H : Subgroup G) (e : G ≃* G') :
    H.equivMapOfInjective (e : G →* G') (EquivLike.injective e) = e.subgroupMap H := by
  ext
  rfl

