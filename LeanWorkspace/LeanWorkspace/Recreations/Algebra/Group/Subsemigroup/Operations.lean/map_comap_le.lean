import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem map_comap_le {S : Subsemigroup N} {f : M →ₙ* N} : (S.comap f).map f ≤ S := (Subsemigroup.gc_map_comap f).l_u_le _

