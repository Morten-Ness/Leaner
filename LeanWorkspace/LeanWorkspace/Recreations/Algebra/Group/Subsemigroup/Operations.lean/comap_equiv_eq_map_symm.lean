import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem comap_equiv_eq_map_symm (f : N ≃* M) (K : Subsemigroup M) :
    K.comap (f : N →ₙ* M) = K.map (f.symm : M →ₙ* N) := (Subsemigroup.map_equiv_eq_comap_symm f.symm K).symm

