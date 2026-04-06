FAIL
import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem card_le_card_group [Finite G] : Nat.card H ≤ Nat.card G := by
  classical
  letI : Finite H := Finite.of_injective ((↑) : H → G) fun _ _ h => Subtype.ext h
  simpa [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective ((↑) : H → G) fun _ _ h => Subtype.ext h
