import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

variable {ι : Type*} {f : M →ₙ* N}

variable (hf : Function.Injective f)

theorem comap_iSup_map_of_injective (S : ι → Subsemigroup M) :
    (⨆ i, (S i).map f).comap f = iSup S := (Subsemigroup.gciMapComap hf).u_iSup_l _

