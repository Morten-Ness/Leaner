FAIL
import Mathlib

variable {R ι : Type*}

variable [AddMonoidWithOne R]

theorem of_one_ne_zero_of_two_eq_zero (h₁ : (1 : R) ≠ 0) (h₂ : (2 : R) = 0) : CharP R 2 where
  cast_eq_zero_iff := by
    intro n
    constructor
    · intro hn
      rw [← Nat.mod_add_div n 2]
      rw [Nat.cast_add, hn, zero_add]
      by_cases h : n % 2 = 0
      · exact dvd_of_modEq_zero h
      · have hm : n % 2 = 1 := by
          omega
        exfalso
        apply h₁
        have : ((n % 2 : ℕ) : R) = 0 := by
          simpa [Nat.cast_mul, h₂, zero_mul] using hn
        simpa [hm] using this
    · intro hn
      rcases hn with ⟨k, rfl⟩
      rw [Nat.cast_mul, h₂, zero_mul]
