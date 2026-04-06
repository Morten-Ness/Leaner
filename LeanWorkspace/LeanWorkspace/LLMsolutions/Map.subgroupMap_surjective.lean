import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem subgroupMap_surjective (f : G →* G') (H : Subgroup G) :
    Function.Surjective (f.subgroupMap H) :=
by
  intro y
  rcases y with ⟨y, hy⟩
  rcases hy with ⟨x, hx, rfl⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  rfl
