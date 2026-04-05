import Mathlib

variable {ι α β M N P G : Type*}

theorem tail_sum (L : List ℕ) : L.tail.sum = L.sum - L.headI := by
  rw [← List.headI_add_tail_sum L, add_comm, Nat.add_sub_cancel_right]

