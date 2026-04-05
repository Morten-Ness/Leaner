import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H K : Subgroup G}

variable {N : Type*} [Group N]

theorem le_normalizer_of_normal [H.Normal] : K ≤ normalizer H := Subgroup.subset_normalizer_of_normal

