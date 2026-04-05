import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

variable {ι : Type*} {f : M →ₙ* N}

variable (hf : Function.Injective f)

theorem comap_inf_map_of_injective (S T : Subsemigroup M) : (S.map f ⊓ T.map f).comap f = S ⊓ T := (Subsemigroup.gciMapComap hf).u_inf_l _ _

