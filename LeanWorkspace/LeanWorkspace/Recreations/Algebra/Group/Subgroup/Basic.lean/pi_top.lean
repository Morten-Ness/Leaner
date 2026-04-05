import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

variable {η : Type*} {f : η → Type*}

variable [∀ i, Group (f i)]

theorem pi_top (I : Set η) : (Subgroup.pi I fun i => (⊤ : Subgroup (f i))) = ⊤ := ext fun x => by simp [Subgroup.mem_pi]

