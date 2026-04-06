FAIL
import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem card_le_one_iff_eq_bot [Finite H] : Nat.card H ≤ 1 ↔ H = ⊥ := by
  constructor
  · intro hcard
    haveI : Fintype H := Fintype.ofFinite H
    have hone : Fintype.card H = 1 := by
      rw [← Nat.card_eq_fintype_card]
      have hpos : 1 ≤ Nat.card H := Nat.card_pos
      omega
    have huni := Fintype.card_eq_one_iff.mp hone
    rcases huni with ⟨x, hx⟩
    ext g
    constructor
    · intro hg
      have hx1 : x = (1 : H) := hx 1
      have hxg : x = ⟨g, hg⟩ := hx ⟨g, hg⟩
      have hsub : (⟨g, hg⟩ : H) = 1 := hxg.symm.trans hx1
      change g = 1
      exact Subtype.mk.inj hsub
    · intro hg
      rw [hsubgroup_iff] at hg
      simpa [hg]
  · intro hbot
    subst hbot
    simp
