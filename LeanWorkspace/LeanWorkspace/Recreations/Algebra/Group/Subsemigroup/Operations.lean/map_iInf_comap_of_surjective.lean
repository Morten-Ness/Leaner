import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

variable {ι : Type*} {f : M →ₙ* N} (hf : Function.Surjective f)

theorem map_iInf_comap_of_surjective (S : ι → Subsemigroup N) :
    (⨅ i, (S i).comap f).map f = iInf S := (Subsemigroup.giMapComap hf).l_iInf_u _

