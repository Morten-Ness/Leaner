import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [IdemSemiring α] {a b c : α}

theorem natCast_eq_one {n : ℕ} (nezero : n ≠ 0) : (n : α) = 1 := by
  rw [← Nat.one_le_iff_ne_zero] at nezero
  induction n, nezero using Nat.le_induction with
  | base => exact Nat.cast_one
  | succ x _ hx => rw [Nat.cast_add, hx, Nat.cast_one, add_idem 1]

