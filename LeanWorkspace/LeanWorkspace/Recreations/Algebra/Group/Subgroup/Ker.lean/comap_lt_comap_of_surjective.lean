import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem comap_lt_comap_of_surjective {f : G →* N} {K L : Subgroup N} (hf : Function.Surjective f) :
    K.comap f < L.comap f ↔ K < L := by simp_rw [lt_iff_le_not_ge, Subgroup.comap_le_comap_of_surjective hf]

