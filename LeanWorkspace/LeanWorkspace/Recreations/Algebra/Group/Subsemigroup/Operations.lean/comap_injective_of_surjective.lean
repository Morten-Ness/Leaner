import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

variable {ι : Type*} {f : M →ₙ* N} (hf : Function.Surjective f)

theorem comap_injective_of_surjective : Function.Injective (Subsemigroup.comap f) := (Subsemigroup.giMapComap hf).u_injective

