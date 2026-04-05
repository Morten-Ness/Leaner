import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem card_le_of_le {H K : Subgroup G} [Finite K] (h : H ≤ K) : Nat.card H ≤ Nat.card K := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective h)

