import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem conjugatesOfSet_mono {s t : Set G} (h : s ⊆ t) : Group.conjugatesOfSet s ⊆ Group.conjugatesOfSet t := Set.biUnion_subset_biUnion_left h

