import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem map_inf (S T : Subsemigroup M) (f : M →ₙ* N) (hf : Function.Injective f) :
    (S ⊓ T).map f = S.map f ⊓ T.map f := SetLike.coe_injective (Set.image_inter hf)

