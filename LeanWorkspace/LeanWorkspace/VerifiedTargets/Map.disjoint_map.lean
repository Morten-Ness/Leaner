import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem disjoint_map {f : G →* N} (hf : Function.Injective f) {H K : Subgroup G} (h : Disjoint H K) :
    Disjoint (H.map f) (K.map f) := by
  rw [disjoint_iff, ← Subgroup.map_inf _ _ f hf, disjoint_iff.mp h, Subgroup.map_bot]

