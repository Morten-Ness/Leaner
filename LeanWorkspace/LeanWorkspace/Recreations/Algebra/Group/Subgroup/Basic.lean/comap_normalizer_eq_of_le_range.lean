import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H K : Subgroup G}

variable {N : Type*} [Group N]

theorem comap_normalizer_eq_of_le_range {f : N →* G} (h : H ≤ f.range) :
    (normalizer H).comap f = normalizer (H.comap f) := by
  apply le_antisymm (Subgroup.le_normalizer_comap f)
  rw [← map_le_iff_le_comap]
  apply (Subgroup.le_normalizer_map f).trans
  rw [map_comap_eq_self h]

