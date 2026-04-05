import Mathlib

variable {ι α β M N G k R : Type*}

variable [DecidableEq α] {s : Finset α} {B : Finset (Finset α)} {n : ℕ}

theorem sum_card_inter (h : ∀ a ∈ s, #{b ∈ B | a ∈ b} = n) :
    (∑ t ∈ B, #(s ∩ t)) = #s * n := (Finset.sum_card_inter_le fun a ha ↦ (h a ha).le).antisymm (Finset.le_sum_card_inter fun a ha ↦ (h a ha).ge)

