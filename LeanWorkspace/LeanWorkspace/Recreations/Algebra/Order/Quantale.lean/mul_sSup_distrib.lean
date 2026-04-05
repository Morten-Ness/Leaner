import Mathlib

variable {α : Type*} {ι : Type*} {x y z : α} {s : Set α} {f : ι → α}

variable [Semigroup α] [CompleteLattice α] [IsQuantale α]

theorem mul_sSup_distrib : x * sSup s = ⨆ y ∈ s, x * y := IsQuantale.mul_sSup_distrib _ _

