import Mathlib

variable {ι α β M N G k R : Type*}

variable [DecidableEq α] {s : Finset α} {B : Finset (Finset α)} {n : ℕ}

theorem le_sum_card_inter (h : ∀ a ∈ s, n ≤ #{b ∈ B | a ∈ b}) : #s * n ≤ ∑ t ∈ B, #(s ∩ t) := by
  apply (s.card_nsmul_le_sum _ _ h).trans
  simp_rw [← filter_mem_eq_inter, card_eq_sum_ones, sum_filter]
  exact sum_comm.le

