import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem subgroupComap_surjective_of_surjective (f : G →* G') (H' : Subgroup G') (hf : Function.Surjective f) :
    Function.Surjective (f.subgroupComap H') := by
  intro x
  rcases hf x.1 with ⟨y, hy⟩
  refine ⟨⟨y, ?_⟩, ?_⟩
  · simpa [hy] using x.2
  · ext
    exact hy
