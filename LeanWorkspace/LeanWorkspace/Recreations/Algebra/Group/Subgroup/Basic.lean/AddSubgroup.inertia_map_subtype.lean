import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem AddSubgroup.inertia_map_subtype {M : Type*} [AddGroup M] (I : AddSubgroup M)
    {G : Type*} [Group G] [MulAction G M] (H : Subgroup G) :
    (I.inertia H).map H.subtype = I.inertia G ⊓ H := by
  rw [← AddSubgroup.subgroupOf_inertia, Subgroup.subgroupOf_map_subtype]

