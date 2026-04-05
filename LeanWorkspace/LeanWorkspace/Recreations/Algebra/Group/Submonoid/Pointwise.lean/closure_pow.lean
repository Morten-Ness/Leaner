import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable {s t u : Set M}

theorem closure_pow {n : ℕ} (hs : 1 ∈ s) (hn : n ≠ 0) : closure (s ^ n) = closure s := (Submonoid.closure_pow_le hn).antisymm <| by gcongr; exact subset_pow hs hn

