import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

variable {ι : Type*} {f : M →ₙ* N}

variable (hf : Function.Injective f)

theorem map_strictMono_of_injective : StrictMono (Subsemigroup.map f) := (Subsemigroup.gciMapComap hf).strictMono_l

