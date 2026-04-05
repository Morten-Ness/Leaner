import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

theorem Bound.pow_le_pow_right_of_le_one_or_one_le [ZeroLEOneClass M₀] [PosMulMono M₀]
    (h : 1 ≤ a ∧ n ≤ m ∨ 0 ≤ a ∧ a ≤ 1 ∧ m ≤ n) :
    a ^ n ≤ a ^ m := by
  obtain ⟨a1, nm⟩ | ⟨a0, a1, mn⟩ := h
  · exact pow_right_mono₀ a1 nm
  · exact pow_le_pow_of_le_one a0 a1 mn

