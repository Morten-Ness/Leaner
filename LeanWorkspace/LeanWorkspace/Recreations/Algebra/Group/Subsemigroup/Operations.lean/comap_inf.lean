import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem comap_inf (S T : Subsemigroup N) (f : M →ₙ* N) : (S ⊓ T).comap f = S.comap f ⊓ T.comap f := (Subsemigroup.gc_map_comap f).u_inf

