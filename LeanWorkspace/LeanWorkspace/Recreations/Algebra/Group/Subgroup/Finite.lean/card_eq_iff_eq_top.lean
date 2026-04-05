import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem card_eq_iff_eq_top [Finite H] : Nat.card H = Nat.card G ↔ H = ⊤ := Iff.intro (Subgroup.eq_top_of_card_eq H) (fun h ↦ by simpa only [h] using Subgroup.card_top)

