import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_le_map_iff_of_injective {f : G →* N} (hf : Function.Injective f) {H K : Subgroup G} :
    H.map f ≤ K.map f ↔ H ≤ K := by rw [map_le_iff_le_comap, Subgroup.comap_map_eq_self_of_injective hf]

