import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem bot_subgroupOf : (⊥ : Subgroup G).subgroupOf H = ⊥ := Eq.symm (Subgroup.ext fun _g => Subtype.ext_iff)

