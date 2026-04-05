import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_injective_of_ker_le {H K : Subgroup G} (hH : f.ker ≤ H) (hK : f.ker ≤ K)
    (hf : map f H = map f K) : H = K := by
  apply_fun comap f at hf
  rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq, sup_of_le_left hH, sup_of_le_left hK] at hf

