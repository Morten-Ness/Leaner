import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem map_bot (f : M →ₙ* N) : (⊥ : Subsemigroup M).map f = ⊥ := (Subsemigroup.gc_map_comap f).l_bot

