import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem le_prod_iff {H : Subgroup G} {K : Subgroup N} {J : Subgroup (G × N)} :
    J ≤ H.prod K ↔ map (MonoidHom.fst G N) J ≤ H ∧ map (MonoidHom.snd G N) J ≤ K := by
  simpa only [← Subgroup.toSubmonoid_le] using Submonoid.le_prod_iff

