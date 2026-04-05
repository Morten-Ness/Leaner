import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_subtype_le_map_subtype {G' : Subgroup G} {H K : Subgroup G'} :
    H.map G'.subtype ≤ K.map G'.subtype ↔ H ≤ K := Subgroup.map_le_map_iff_of_injective G'.subtype_injective

