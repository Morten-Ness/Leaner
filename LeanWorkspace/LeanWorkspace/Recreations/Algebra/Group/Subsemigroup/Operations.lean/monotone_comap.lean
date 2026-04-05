import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem monotone_comap {f : M →ₙ* N} : Monotone (Subsemigroup.comap f) := (Subsemigroup.gc_map_comap f).monotone_u

