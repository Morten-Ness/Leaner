import Mathlib

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {n : ℕ}

theorem isMaxChain_range_flag (b : Module.Basis (Fin n) K V) : IsMaxChain (· ≤ ·) (Set.range b.flag) := b.toFlag.maxChain

