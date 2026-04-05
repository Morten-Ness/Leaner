import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

variable {ι : Type*} {f : M →ₙ* N} (hf : Function.Surjective f)

theorem map_surjective_of_surjective : Function.Surjective (Subsemigroup.map f) := (Subsemigroup.giMapComap hf).l_surjective

