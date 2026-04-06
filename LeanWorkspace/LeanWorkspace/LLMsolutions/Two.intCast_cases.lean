FAIL
import Mathlib

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem intCast_cases (n : ℤ) : (n : R) = 0 ∨ (n : R) = 1 := by
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    rw [hk, Int.cast_add]
    have h2 : (2 : R) = 0 := CharP.cast_eq_zero (R := R) 2
    calc
      (k : R) + (k : R) = (2 : R) * (k : R) := by ring
      _ = 0 := by rw [h2, zero_mul]
  · right
    rw [hk, Int.cast_add]
    have h2 : (2 : R) = 0 := CharP.cast_eq_zero (R := R) 2
    calc
      (k : R) + ((k : R) + 1) = ((k : R) + (k : R)) + 1 := by abel
      _ = 0 + 1 := by rw [show (k : R) + (k : R) = (2 : R) * (k : R) by ring, h2, zero_mul]
      _ = 1 := by simp
