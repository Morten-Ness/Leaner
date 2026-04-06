FAIL
import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem eq_top_of_card_eq [Finite H] (h : Nat.card H = Nat.card G) : H = ⊤ := by
  classical
  by_contra hne
  have hproper : H ≠ ⊤ := hne
  have hlt : Nat.card H < Nat.card G := by
    simpa using Subgroup.card_lt_card (H := H) hproper
  exact (ne_of_lt hlt) h
