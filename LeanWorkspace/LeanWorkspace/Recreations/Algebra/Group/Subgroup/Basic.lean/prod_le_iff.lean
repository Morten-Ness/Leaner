import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem prod_le_iff {H : Subgroup G} {K : Subgroup N} {J : Subgroup (G × N)} :
    H.prod K ≤ J ↔ map (MonoidHom.inl G N) H ≤ J ∧ map (MonoidHom.inr G N) K ≤ J := by
  simpa only [← Subgroup.toSubmonoid_le] using Submonoid.prod_le_iff

