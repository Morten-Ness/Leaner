import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem prod_eq_bot_iff {H : Subgroup G} {K : Subgroup N} : H.prod K = ⊥ ↔ H = ⊥ ∧ K = ⊥ := by
  simpa only [← Subgroup.toSubmonoid_inj] using Submonoid.prod_eq_bot_iff

