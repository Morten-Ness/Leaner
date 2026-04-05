import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem map_le_of_le_comap {T : Subsemigroup N} {f : M →ₙ* N} : S ≤ T.comap f → S.map f ≤ T := (Subsemigroup.gc_map_comap f).l_le

