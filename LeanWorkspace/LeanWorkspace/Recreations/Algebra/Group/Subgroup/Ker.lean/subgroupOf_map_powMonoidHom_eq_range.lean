import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

variable {M : Type*} [CommGroup M]

theorem subgroupOf_map_powMonoidHom_eq_range (S : Subgroup M) (n : ℕ) :
    (map (powMonoidHom n) S).subgroupOf S = (powMonoidHom n).range := by
  ext : 1
  simp [mem_subgroupOf]
  grind

