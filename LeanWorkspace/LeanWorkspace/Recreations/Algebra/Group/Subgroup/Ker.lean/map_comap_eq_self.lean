import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_comap_eq_self {f : G →* N} {H : Subgroup N} (h : H ≤ f.range) :
    map f (comap f H) = H := by
  rwa [Subgroup.map_comap_eq, inf_eq_right]

