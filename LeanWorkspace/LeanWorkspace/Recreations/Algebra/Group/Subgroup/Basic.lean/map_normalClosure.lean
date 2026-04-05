import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem map_normalClosure (s : Set G) (f : G →* N) (hf : Function.Surjective f) :
    (Subgroup.normalClosure s).map f = Subgroup.normalClosure (f '' s) := by
  have : Normal (map f (Subgroup.normalClosure s)) := Subgroup.Normal.map inferInstance f hf
  apply le_antisymm
  · simp [map_le_iff_le_comap, Subgroup.normalClosure_le_normal, coe_comap,
      ← Set.image_subset_iff, Subgroup.subset_normalClosure]
  · exact Subgroup.normalClosure_le_normal (Set.image_mono Subgroup.subset_normalClosure)

