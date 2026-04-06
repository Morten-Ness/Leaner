import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_eq_range_iff {f : G →* N} {H : Subgroup G} :
    H.map f = f.range ↔ Codisjoint H f.ker := by
  rw [Subgroup.map_eq_range_iff]
