import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

variable {ι : Type*} {f : M →ₙ* N}

variable (hf : Function.Injective f)

theorem map_injective_of_injective : Function.Injective (Subsemigroup.map f) := (Subsemigroup.gciMapComap hf).l_injective

