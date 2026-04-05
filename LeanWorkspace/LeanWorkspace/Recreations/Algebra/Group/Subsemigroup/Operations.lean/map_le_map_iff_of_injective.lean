import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

variable {ι : Type*} {f : M →ₙ* N}

variable (hf : Function.Injective f)

theorem map_le_map_iff_of_injective {S T : Subsemigroup M} : S.map f ≤ T.map f ↔ S ≤ T := (Subsemigroup.gciMapComap hf).l_le_l_iff

