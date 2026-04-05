import Mathlib

variable {α : Type*} {ι : Type*} {x y z : α} {s : Set α} {f : ι → α}

variable [Semigroup α] [CompleteLattice α] [IsQuantale α]

theorem sup_mul_distrib : (x ⊔ y) * z = (x * z) ⊔ (y * z) := by
  rw [← (@iSup_pair _ _ _ (fun _? => _? * z) _ _), ← sSup_pair, sSup_mul_distrib]

