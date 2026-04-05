import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem top_prod_top : (⊤ : Subgroup G).prod (⊤ : Subgroup N) = ⊤ := (Subgroup.top_prod _).trans <| comap_top _

