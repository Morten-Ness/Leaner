import Mathlib

variable {α β : Type*}

variable [DecidableEq α] {s : Multiset α}

theorem count_nsmul (a : α) (n s) : count a (n • s) = n * count a s := by
  induction n <;> simp [*, succ_nsmul, succ_mul, zero_nsmul]

