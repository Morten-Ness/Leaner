import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

variable {ι : Type*} {f : M →ₙ* N}

variable (hf : Function.Injective f)

theorem comap_iInf_map_of_injective (S : ι → Subsemigroup M) :
    (⨅ i, (S i).map f).comap f = iInf S := (Subsemigroup.gciMapComap hf).u_iInf_l _

