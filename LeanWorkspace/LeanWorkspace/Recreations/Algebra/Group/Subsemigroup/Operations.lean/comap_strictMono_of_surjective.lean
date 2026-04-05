import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

variable {ι : Type*} {f : M →ₙ* N} (hf : Function.Surjective f)

theorem comap_strictMono_of_surjective : StrictMono (Subsemigroup.comap f) := (Subsemigroup.giMapComap hf).strictMono_u

