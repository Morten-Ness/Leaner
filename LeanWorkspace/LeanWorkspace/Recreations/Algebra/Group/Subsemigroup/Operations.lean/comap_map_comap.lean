import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem comap_map_comap {S : Subsemigroup N} {f : M →ₙ* N} :
    ((S.comap f).map f).comap f = S.comap f := (Subsemigroup.gc_map_comap f).u_l_u_eq_u _

