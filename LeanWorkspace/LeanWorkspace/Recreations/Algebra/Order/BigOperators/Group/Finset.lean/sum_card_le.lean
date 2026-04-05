import Mathlib

variable {ι α β M N G k R : Type*}

variable [DecidableEq α] {s : Finset α} {B : Finset (Finset α)} {n : ℕ}

theorem sum_card_le [Fintype α] (h : ∀ a, #{b ∈ B | a ∈ b} ≤ n) : ∑ s ∈ B, #s ≤ Fintype.card α * n := calc
    ∑ s ∈ B, #s = ∑ s ∈ B, #(univ ∩ s) := by simp_rw [univ_inter]
    _ ≤ Fintype.card α * n := Finset.sum_card_inter_le fun a _ ↦ h a

