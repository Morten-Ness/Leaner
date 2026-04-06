import Mathlib

variable {ι α β M N P G : Type*}

theorem headI_le_sum (L : List ℕ) : L.headI ≤ L.sum := by
  cases L with
  | nil =>
      simp
  | cons a t =>
      simp [List.headI, Nat.le_add_right]
