import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem map_comap_map {f : M →ₙ* N} : ((S.map f).comap f).map f = S.map f := (Subsemigroup.gc_map_comap f).l_u_l_eq_l _

