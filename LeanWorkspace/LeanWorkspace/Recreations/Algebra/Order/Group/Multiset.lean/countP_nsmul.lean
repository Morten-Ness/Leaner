import Mathlib

variable {α β : Type*}

variable (p : α → Prop) [DecidablePred p]

theorem countP_nsmul (s) (n : ℕ) : countP p (n • s) = n * countP p s := by
  induction n <;> simp [*, succ_nsmul, succ_mul, zero_nsmul]

