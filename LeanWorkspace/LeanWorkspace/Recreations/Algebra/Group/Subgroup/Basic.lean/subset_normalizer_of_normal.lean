import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H K : Subgroup G}

variable {N : Type*} [Group N]

theorem subset_normalizer_of_normal {S : Set G} [hH : H.Normal] : S ⊆ normalizer (H : Set G) := (@Subgroup.normalizer_eq_top _ _ H hH) ▸ le_top

