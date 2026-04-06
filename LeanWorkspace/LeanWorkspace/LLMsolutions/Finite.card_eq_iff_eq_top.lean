FAIL
import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem card_eq_iff_eq_top [Finite H] : Nat.card H = Nat.card G ↔ H = ⊤ := by
  constructor
  · intro hcard
    by_contra hne
    have hproper : H < ⊤ := lt_top_iff_ne_top.mpr hne
    have hindex_ne_one : H.index ≠ 1 := by
      intro h1
      exact hproper.ne (Subgroup.index_eq_one.mp h1)
    have hindex_dvd : H.index ∣ Nat.card G := by
      simpa [Subgroup.index] using Subgroup.card_subgroup_dvd_card (H := H)
    have hindex_two_le : 2 ≤ H.index := by
      omega
    have hGfinite : Finite G := by
      rw [← hcard]
      infer_instance
    have hcard_mul : Nat.card G = Nat.card H * H.index := by
      simpa [Nat.mul_comm] using (Subgroup.card_mul_index (H := H)).symm
    rw [hcard] at hcard_mul
    have hpos : 0 < Nat.card H := Nat.card_pos
    have hone_lt : 1 < H.index := lt_of_lt_of_le (by omega) hindex_two_le
    have hlt : Nat.card H < Nat.card H * H.index := by
      simpa [one_mul] using Nat.mul_lt_mul_of_pos_left hone_lt hpos
    omega
  · intro htop
    subst htop
    simp
