import Mathlib

variable {ι α β M N G k R : Type*}

variable [DecidableEq α] {s : Finset α} {B : Finset (Finset α)} {n : ℕ}

theorem sum_card_inter_le (h : ∀ a ∈ s, #{b ∈ B | a ∈ b} ≤ n) : (∑ t ∈ B, #(s ∩ t)) ≤ #s * n := by
  refine le_trans ?_ (s.sum_le_card_nsmul _ _ h)
  simp_rw [← filter_mem_eq_inter, card_eq_sum_ones, sum_filter]
  exact sum_comm.le

