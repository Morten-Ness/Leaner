import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem card_top : Nat.card (⊤ : Subgroup G) = Nat.card G := Nat.card_congr Subgroup.topEquiv.toEquiv

