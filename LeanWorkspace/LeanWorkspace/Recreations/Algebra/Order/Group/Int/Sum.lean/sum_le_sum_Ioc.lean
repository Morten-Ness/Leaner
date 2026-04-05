import Mathlib

theorem sum_le_sum_Ioc {s : Finset ℤ} {c : ℤ} (hs : ∀ x ∈ s, x ≤ c) :
    ∑ x ∈ s, x ≤ ∑ x ∈ Ioc (c - #s) c, x := by
  set r := Ioc (c - #s) c
  calc
    _ ≤ ∑ x ∈ s ∩ r, x + #(s \ r) • (c - #s) := by
      rw [← sum_inter_add_sum_diff s r _]
      gcongr
      apply sum_le_card_nsmul
      grind
    _ = ∑ x ∈ r ∩ s, x + #(r \ s) • (c - #s) := by
      rw [inter_comm, card_sdiff_comm]
      rw [Int.card_Ioc, sub_sub_cancel, Int.toNat_natCast]
    _ ≤ _ := by
      rw [← sum_inter_add_sum_diff r s _]
      gcongr
      refine card_nsmul_le_sum _ _ _ fun x mx ↦ ?_
      rw [mem_sdiff, mem_Ioc] at mx; exact mx.1.1.le

