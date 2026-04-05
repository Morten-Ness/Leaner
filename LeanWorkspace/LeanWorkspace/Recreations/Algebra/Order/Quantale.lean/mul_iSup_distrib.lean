import Mathlib

variable {α : Type*} {ι : Type*} {x y z : α} {s : Set α} {f : ι → α}

variable [Semigroup α] [CompleteLattice α] [IsQuantale α]

theorem mul_iSup_distrib : x * ⨆ i, f i = ⨆ i, x * f i := by
  rw [iSup, mul_sSup_distrib, iSup_range]

