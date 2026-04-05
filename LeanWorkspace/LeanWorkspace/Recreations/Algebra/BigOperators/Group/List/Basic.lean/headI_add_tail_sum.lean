import Mathlib

variable {ι α β M N P G : Type*}

theorem headI_add_tail_sum (L : List ℕ) : L.headI + L.tail.sum = L.sum := by
  cases L <;> simp

