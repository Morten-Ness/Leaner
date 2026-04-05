import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem eq_top_of_card_eq [Finite H] (h : Nat.card H = Nat.card G) : H = ⊤ := by
  have : Finite G := Nat.finite_of_card_ne_zero (h ▸ Nat.card_pos.ne')
  exact Subgroup.eq_top_of_le_card _ (Nat.le_of_eq h.symm)

