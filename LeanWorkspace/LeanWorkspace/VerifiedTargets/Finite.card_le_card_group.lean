import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem card_le_card_group [Finite G] : Nat.card H ≤ Nat.card G := Nat.card_le_card_of_injective _ Subtype.coe_injective

