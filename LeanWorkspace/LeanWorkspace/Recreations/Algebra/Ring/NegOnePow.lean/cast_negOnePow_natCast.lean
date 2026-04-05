import Mathlib

theorem cast_negOnePow_natCast (R : Type*) [Ring R] (n : ℕ) : Int.negOnePow n = (-1 : R) ^ n := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n <;> simp [pow_succ, pow_mul]

