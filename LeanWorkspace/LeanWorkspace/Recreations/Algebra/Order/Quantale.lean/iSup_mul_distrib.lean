import Mathlib

variable {α : Type*} {ι : Type*} {x y z : α} {s : Set α} {f : ι → α}

variable [Semigroup α] [CompleteLattice α] [IsQuantale α]

theorem iSup_mul_distrib : (⨆ i, f i) * x = ⨆ i, f i * x := by
  rw [iSup, sSup_mul_distrib, iSup_range]

