FAIL
import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R] (p : ℕ)

variable [CharP R p] {a b : ℕ}

theorem natCast_eq_natCast_mod (a : ℕ) : (a : R) = a % p := by
  induction' a using Nat.mod.inductionOn with a ih
  · simp
  · rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · rw [Nat.mod_eq_sub_mod hp (Nat.le_add_right _ _)]
      rw [Nat.cast_add, CharP.cast_eq_zero]
      simp [ih]
