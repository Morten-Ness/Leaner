import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem map_sup (S T : Subsemigroup M) (f : M →ₙ* N) : (S ⊔ T).map f = S.map f ⊔ T.map f := (Subsemigroup.gc_map_comap f).l_sup

