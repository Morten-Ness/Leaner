import Mathlib

variable {α : Type*} {ι : Type*} {x y z : α} {s : Set α} {f : ι → α}

variable [Semigroup α] [CompleteLattice α] [IsQuantale α]

theorem mul_sup_distrib : x * (y ⊔ z) = (x * y) ⊔ (x * z) := by
  rw [← iSup_pair, ← sSup_pair, mul_sSup_distrib]

