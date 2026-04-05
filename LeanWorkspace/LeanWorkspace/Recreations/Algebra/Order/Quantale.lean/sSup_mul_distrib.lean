import Mathlib

variable {α : Type*} {ι : Type*} {x y z : α} {s : Set α} {f : ι → α}

variable [Semigroup α] [CompleteLattice α] [IsQuantale α]

theorem sSup_mul_distrib : sSup s * x = ⨆ y ∈ s, y * x := IsQuantale.sSup_mul_distrib _ _

