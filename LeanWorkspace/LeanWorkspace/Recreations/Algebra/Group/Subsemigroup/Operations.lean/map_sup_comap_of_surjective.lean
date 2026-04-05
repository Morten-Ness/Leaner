import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

variable {ι : Type*} {f : M →ₙ* N} (hf : Function.Surjective f)

theorem map_sup_comap_of_surjective (S T : Subsemigroup N) :
    (S.comap f ⊔ T.comap f).map f = S ⊔ T := (Subsemigroup.giMapComap hf).l_sup_u _ _

