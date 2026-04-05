import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem map_iSup {ι : Sort*} (f : M →ₙ* N) (s : ι → Subsemigroup M) :
    (iSup s).map f = ⨆ i, (s i).map f := (Subsemigroup.gc_map_comap f).l_iSup

