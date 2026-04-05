import Mathlib

variable {ι α β M N P G : Type*}

theorem headI_le_sum (L : List ℕ) : L.headI ≤ L.sum := Nat.le.intro (List.headI_add_tail_sum L)

