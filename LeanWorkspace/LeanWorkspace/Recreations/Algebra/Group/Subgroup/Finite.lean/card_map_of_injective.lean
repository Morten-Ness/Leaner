import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem card_map_of_injective {H : Type*} [Group H] {K : Subgroup G} {f : G →* H}
    (hf : Function.Injective f) :
    Nat.card (map f K) = Nat.card K := by
  apply Nat.card_image_of_injective hf

