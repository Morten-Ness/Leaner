import Mathlib

variable {ι α β M N G k R : Type*}

variable [DecidableEq α] {s : Finset α} {B : Finset (Finset α)} {n : ℕ}

theorem sum_card [Fintype α] (h : ∀ a, #{b ∈ B | a ∈ b} = n) :
    ∑ s ∈ B, #s = Fintype.card α * n := by
  simp_rw [Fintype.card, ← Finset.sum_card_inter fun a _ ↦ h a, univ_inter]

