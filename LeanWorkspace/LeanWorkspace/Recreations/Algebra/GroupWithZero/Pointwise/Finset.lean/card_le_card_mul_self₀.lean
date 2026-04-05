import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [Zero α] [DecidableEq α] {s t : Finset α} {a : α}

theorem card_le_card_mul_self₀ [IsLeftCancelMulZero α] : #s ≤ #(s * s) := by
  obtain hs | hs := (s.erase 0).eq_empty_or_nonempty
  · rw [erase_eq_empty_iff] at hs
    obtain rfl | rfl := hs <;> simp
  obtain ⟨a, ha⟩ := hs
  simp only [mem_erase, ne_eq] at ha
  exact Finset.card_le_card_mul_left₀ ha.2 ha.1

