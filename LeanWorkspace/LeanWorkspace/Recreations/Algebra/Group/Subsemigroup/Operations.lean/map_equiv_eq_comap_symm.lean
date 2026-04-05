import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem map_equiv_eq_comap_symm (f : M ≃* N) (K : Subsemigroup M) :
    K.map (f : M →ₙ* N) = K.comap (f.symm : N →ₙ* M) := SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

