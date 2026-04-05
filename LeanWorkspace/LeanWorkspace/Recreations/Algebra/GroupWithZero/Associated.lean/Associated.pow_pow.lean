import Mathlib

variable {M : Type*}

theorem Associated.pow_pow [CommMonoid M] {a b : M} {n : ℕ} (h : a ~ᵤ b) : a ^ n ~ᵤ b ^ n := by
  induction n with
  | zero => simp [Associated.refl]
  | succ n ih => convert h.mul_mul ih <;> rw [pow_succ']

