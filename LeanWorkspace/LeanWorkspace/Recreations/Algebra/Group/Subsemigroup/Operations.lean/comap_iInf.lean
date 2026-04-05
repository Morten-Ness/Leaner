import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem comap_iInf {ι : Sort*} (f : M →ₙ* N) (s : ι → Subsemigroup N) :
    (iInf s).comap f = ⨅ i, (s i).comap f := (Subsemigroup.gc_map_comap f).u_iInf

