import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_le_map_iff' {f : G →* N} {H K : Subgroup G} :
    H.map f ≤ K.map f ↔ H ⊔ f.ker ≤ K ⊔ f.ker := by
  simpa [Subgroup.map_le_iff_le_comap, Subgroup.comap_map_eq, sup_comm, sup_assoc] using
    (Subgroup.map_le_map_iff (f := f) (H := H) (K := K))
