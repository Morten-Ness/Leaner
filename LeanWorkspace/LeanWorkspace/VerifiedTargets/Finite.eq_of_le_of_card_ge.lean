import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem eq_of_le_of_card_ge {H K : Subgroup G} [Finite K] (hle : H ≤ K)
    (hcard : Nat.card K ≤ Nat.card H) :
    H = K := SetLike.coe_injective <| Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hle hcard

