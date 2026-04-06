import Mathlib

variable {ι α β M N P G : Type*}

theorem tail_sum (L : List ℕ) : L.tail.sum = L.sum - L.headI := by
  cases L with
  | nil =>
      simp
  | cons a t =>
      simp [List.headI, Nat.add_sub_cancel_left]
