import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

variable {ι : Type*} {f : M →ₙ* N} (hf : Function.Surjective f)

theorem map_comap_eq_of_surjective (S : Subsemigroup N) : (S.comap f).map f = S := (Subsemigroup.giMapComap hf).l_u_eq _

