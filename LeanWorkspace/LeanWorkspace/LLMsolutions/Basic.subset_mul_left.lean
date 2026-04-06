import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [MulOneClass α]

theorem subset_mul_left (s : Finset α) {t : Finset α} (ht : (1 : α) ∈ t) : s ⊆ s * t := by
  intro a ha
  rw [Finset.mem_mul]
  exact ⟨a, ha, 1, ht, by simp⟩
