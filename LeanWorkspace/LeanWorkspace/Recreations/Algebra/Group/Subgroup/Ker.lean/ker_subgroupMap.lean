import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem ker_subgroupMap : (f.subgroupMap H).ker = f.ker.subgroupOf H := ext fun _ ↦ Subtype.ext_iff

