import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

variable {ι : Type*} {f : M →ₙ* N}

variable (hf : Function.Injective f)

theorem comap_surjective_of_injective : Function.Surjective (Subsemigroup.comap f) := (Subsemigroup.gciMapComap hf).u_surjective

