import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem conjugatesOfSet_subset {s : Set G} {N : Subgroup G} [N.Normal] (h : s ⊆ N) :
    Group.conjugatesOfSet s ⊆ N := Set.iUnion₂_subset fun _x H => Group.conjugates_subset_normal (h H)

