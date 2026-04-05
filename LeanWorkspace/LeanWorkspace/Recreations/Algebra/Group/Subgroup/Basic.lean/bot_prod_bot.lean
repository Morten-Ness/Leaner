import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem bot_prod_bot : (⊥ : Subgroup G).prod (⊥ : Subgroup N) = ⊥ := SetLike.coe_injective <| by simp [Subgroup.coe_prod]

