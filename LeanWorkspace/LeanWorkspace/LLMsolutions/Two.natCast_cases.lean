FAIL
import Mathlib

variable {R ι : Type*}

variable [AddMonoidWithOne R]

variable [CharP R 2]

theorem natCast_cases (n : ℕ) : (n : R) = 0 ∨ (n : R) = 1 := by
  rcases Nat.even_or_odd n with h | h
  · left
    rcases h with ⟨k, rfl⟩
    rw [Nat.cast_add, Nat.cast_mul, show (2 : R) = 0 by exact CharP.cast_eq_zero (R := R) 2]
    simp
  · right
    rcases h with ⟨k, rfl⟩
    rw [Nat.cast_add, Nat.cast_mul, show (2 : R) = 0 by exact CharP.cast_eq_zero (R := R) 2]
    simp
