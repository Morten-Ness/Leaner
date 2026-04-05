import Mathlib

section

open scoped Pointwise

variable {α : Type*}

variable [GroupWithZero α] [DecidableEq α] {s : Finset α}

theorem Nonempty.div_zero (hs : s.Nonempty) : s / 0 = 0 := Finset.div_zero_subset s.antisymm <| by simpa [mem_div] using hs

end

section

open scoped Pointwise

variable {α : Type*}

variable [DecidableEq α] [MulZeroClass α] {s : Finset α}

theorem Nonempty.mul_zero (hs : s.Nonempty) : s * 0 = 0 := Finset.mul_zero_subset s.antisymm <| by simpa [mem_mul] using hs

end

section

open scoped Pointwise

variable {α : Type*}

variable [GroupWithZero α] [DecidableEq α] {s : Finset α}

theorem Nonempty.zero_div (hs : s.Nonempty) : 0 / s = 0 := Finset.zero_div_subset s.antisymm <| by simpa [mem_div] using hs

end

section

open scoped Pointwise

variable {α : Type*}

variable [DecidableEq α] [MulZeroClass α] {s : Finset α}

theorem Nonempty.zero_mul (hs : s.Nonempty) : 0 * s = 0 := Finset.zero_mul_subset s.antisymm <| by simpa [mem_mul] using hs

end

section

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [Zero α] [DecidableEq α] {s t : Finset α} {a : α}

theorem card_le_card_mul_left₀ [IsLeftCancelMulZero α] (has : a ∈ s) (ha : a ≠ 0) : #t ≤ #(s * t) := card_le_card_mul_left_of_injective has (mul_right_injective₀ ha)

end

section

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [Zero α] [DecidableEq α] {s t : Finset α} {a : α}

theorem card_le_card_mul_right₀ [IsRightCancelMulZero α] (hat : a ∈ t) (ha : a ≠ 0) : #s ≤ #(s * t) := card_le_card_mul_right_of_injective hat (mul_left_injective₀ ha)

end

section

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

end
