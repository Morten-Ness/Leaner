import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem le_comap_map {f : M →ₙ* N} : S ≤ (S.map f).comap f := (Subsemigroup.gc_map_comap f).le_u_l _

