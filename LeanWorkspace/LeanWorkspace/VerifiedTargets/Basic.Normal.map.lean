import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

theorem Normal.map {H : Subgroup G} (h : H.Normal) (f : G →* N) (hf : Function.Surjective f) :
    (H.map f).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, ← top_le_iff, ← f.range_eq_top_of_surjective hf, f.range_eq_map,
    ← H.normalizer_eq_top]
  exact Subgroup.le_normalizer_map _

