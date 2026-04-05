import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

variable {η : Type*} {f : η → Type*}

variable [∀ i, Group (f i)]

theorem pi_eq_bot_iff (H : ∀ i, Subgroup (f i)) : Subgroup.pi Set.univ H = ⊥ ↔ ∀ i, H i = ⊥ := by
  simp_rw [SetLike.ext'_iff]
  exact Set.univ_pi_eq_singleton_iff

