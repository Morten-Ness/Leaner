import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H K : Subgroup G}

variable {N : Type*} [Group N]

theorem inf_normalizer_le_normalizer_inf :
    normalizer H ⊓ normalizer K ≤ normalizer ((H ⊓ K :) : Set G) := fun _ h g ↦ and_congr (h.1 g) (h.2 g)

