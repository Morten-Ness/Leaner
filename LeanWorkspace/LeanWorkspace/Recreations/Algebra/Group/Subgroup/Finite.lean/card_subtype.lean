import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem card_subtype (K : Subgroup G) (L : Subgroup K) :
    Nat.card (map K.subtype L) = Nat.card L := Subgroup.card_map_of_injective K.subtype_injective

