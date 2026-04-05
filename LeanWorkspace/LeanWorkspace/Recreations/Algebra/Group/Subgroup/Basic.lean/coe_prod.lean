import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem coe_prod (H : Subgroup G) (K : Subgroup N) :
    (H.prod K : Set (G × N)) = (H : Set G) ×ˢ (K : Set N) := rfl

