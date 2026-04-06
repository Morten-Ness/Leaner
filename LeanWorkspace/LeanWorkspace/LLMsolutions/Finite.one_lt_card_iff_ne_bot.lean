import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem one_lt_card_iff_ne_bot [Finite H] : 1 < Nat.card H ↔ H ≠ ⊥ := by
  constructor
  · intro hcard hbot
    subst hbot
    simp at hcard
  · intro hne
    by_contra hnot
    have hle : Nat.card H ≤ 1 := Nat.not_lt.mp hnot
    have hpos : 0 < Nat.card H := Finite.card_pos_iff.mpr ⟨(1 : H)⟩
    have hone : Nat.card H = 1 := Nat.le_antisymm hle (Nat.succ_le_of_lt hpos)
    letI : Fintype H := Fintype.ofFinite H
    have hcard1 : Fintype.card H = 1 := by simpa using hone
    have hex : ∃ x : H, ∀ y : H, y = x := Fintype.card_eq_one_iff.mp hcard1
    have hbot : H = ⊥ := by
      rcases hex with ⟨x, hx⟩
      have hx1 : x = 1 := by simpa using (hx 1).symm
      ext g
      constructor
      · intro hg
        have hEq : (⟨g, hg⟩ : H) = 1 := by
          calc
            (⟨g, hg⟩ : H) = x := hx _ 
            _ = 1 := hx1
        simpa using congrArg Subtype.val hEq
      · intro hg
        rw [Subgroup.mem_bot] at hg
        simpa [hg]
    exact hne hbot
