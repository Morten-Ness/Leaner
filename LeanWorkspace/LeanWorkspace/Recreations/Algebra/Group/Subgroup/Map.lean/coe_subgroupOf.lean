import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem coe_subgroupOf (H K : Subgroup G) : (H.subgroupOf K : Set K) = K.subtype ⁻¹' H := rfl

