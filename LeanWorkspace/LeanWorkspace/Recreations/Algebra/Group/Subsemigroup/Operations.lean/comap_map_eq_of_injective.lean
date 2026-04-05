import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

variable {ι : Type*} {f : M →ₙ* N}

variable (hf : Function.Injective f)

theorem comap_map_eq_of_injective (S : Subsemigroup M) : (S.map f).comap f = S := (Subsemigroup.gciMapComap hf).u_l_eq _

