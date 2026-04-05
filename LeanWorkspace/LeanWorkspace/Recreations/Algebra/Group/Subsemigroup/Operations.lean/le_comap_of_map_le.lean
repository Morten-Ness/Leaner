import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem le_comap_of_map_le {T : Subsemigroup N} {f : M →ₙ* N} : S.map f ≤ T → S ≤ T.comap f := (Subsemigroup.gc_map_comap f).le_u

