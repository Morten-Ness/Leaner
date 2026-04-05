import Mathlib

variable {α : Type*} {ι : Type*} {x y z : α} {s : Set α} {f : ι → α}

variable [Semigroup α] [CompleteLattice α] [IsQuantale α]

variable {α : Type*} [Semigroup α] [CompleteLattice α] [IsQuantale α]

variable {x : α}

theorem bot_mul : ⊥ * x = ⊥ := by
  rw [← sSup_empty, sSup_mul_distrib]
  simp only [Set.mem_empty_iff_false, not_false_eq_true, iSup_neg, iSup_bot, sSup_empty]

