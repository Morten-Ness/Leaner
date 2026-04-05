import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem codisjoint_subgroupOf_sup (H K : Subgroup G) :
    Codisjoint (H.subgroupOf (H ⊔ K)) (K.subgroupOf (H ⊔ K)) := by
  rw [codisjoint_iff, ← Subgroup.subgroupOf_sup, subgroupOf_self]
  exacts [le_sup_left, le_sup_right]

