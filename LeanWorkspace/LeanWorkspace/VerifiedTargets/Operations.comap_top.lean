import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem comap_top (f : M →ₙ* N) : (⊤ : Subsemigroup N).comap f = ⊤ := (Subsemigroup.gc_map_comap f).u_top

