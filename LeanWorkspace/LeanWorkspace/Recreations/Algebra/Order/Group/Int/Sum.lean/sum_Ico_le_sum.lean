import Mathlib

theorem sum_Ico_le_sum {s : Finset ℤ} {c : ℤ} (hs : ∀ x ∈ s, c ≤ x) :
    ∑ x ∈ Ico c (c + #s), x ≤ ∑ x ∈ s, x := by
  set r := Ico c (c + #s)
  calc
    _ ≤ ∑ x ∈ r ∩ s, x + #(r \ s) • (c + #s) := by
      grw [← sum_inter_add_sum_diff r s, ← sum_le_card_nsmul _ _ _ fun x mx ↦ ?_]
      rw [mem_sdiff, mem_Ico] at mx; exact mx.1.2.le
    _ = ∑ x ∈ s ∩ r, x + #(s \ r) • (c + #s) := by
      rw [inter_comm, card_sdiff_comm]
      rw [Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast]
    _ ≤ _ := by
      grw [← sum_inter_add_sum_diff s r, card_nsmul_le_sum _ _ _ fun x mx ↦ ?_]
      grind

