import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem AddSubgroup.subgroupOf_inertia {M : Type*} [AddGroup M] (I : AddSubgroup M)
    {G : Type*} [Group G] [MulAction G M] (H : Subgroup G) :
    (I.inertia G).subgroupOf H = I.inertia H := rfl

