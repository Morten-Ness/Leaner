import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

variable {η : Type*} {f : η → Type*}

variable [∀ i, Group (f i)]

theorem le_pi_iff {I : Set η} {H : ∀ i, Subgroup (f i)} {J : Subgroup (∀ i, f i)} :
    J ≤ Subgroup.pi I H ↔ ∀ i ∈ I, J ≤ comap (Pi.evalMonoidHom f i) (H i) := Set.subset_pi_iff

