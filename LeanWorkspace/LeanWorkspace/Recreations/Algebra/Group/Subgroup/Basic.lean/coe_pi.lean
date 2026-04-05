import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

variable {η : Type*} {f : η → Type*}

variable [∀ i, Group (f i)]

theorem coe_pi (I : Set η) (H : ∀ i, Subgroup (f i)) :
    (Subgroup.pi I H : Set (∀ i, f i)) = Set.pi I fun i => (H i : Set (f i)) := rfl

