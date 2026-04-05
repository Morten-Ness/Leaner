import Mathlib

variable {ι α β M N G k R : Type*}

variable [DecidableEq α] {s : Finset α} {B : Finset (Finset α)} {n : ℕ}

theorem le_sum_card [Fintype α] (h : ∀ a, n ≤ #{b ∈ B | a ∈ b}) :
    Fintype.card α * n ≤ ∑ s ∈ B, #s := calc
    Fintype.card α * n ≤ ∑ s ∈ B, #(univ ∩ s) := Finset.le_sum_card_inter fun a _ ↦ h a
    _ = ∑ s ∈ B, #s := by simp_rw [univ_inter]

