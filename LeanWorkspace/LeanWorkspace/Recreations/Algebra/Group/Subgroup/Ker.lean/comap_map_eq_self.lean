import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem comap_map_eq_self {f : G →* N} {H : Subgroup G} (h : f.ker ≤ H) :
    comap f (map f H) = H := by
  rwa [Subgroup.comap_map_eq, sup_eq_left]

