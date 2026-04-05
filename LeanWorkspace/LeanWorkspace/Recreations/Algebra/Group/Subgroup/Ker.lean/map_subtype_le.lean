import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_subtype_le {H : Subgroup G} (K : Subgroup H) : K.map H.subtype ≤ H := (K.map_le_range H.subtype).trans_eq H.range_subtype

