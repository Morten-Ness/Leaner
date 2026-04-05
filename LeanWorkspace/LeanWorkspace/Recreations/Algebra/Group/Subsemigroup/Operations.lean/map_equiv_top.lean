import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem map_equiv_top (f : M ≃* N) : (⊤ : Subsemigroup M).map (f : M →ₙ* N) = ⊤ := SetLike.coe_injective <| Set.image_univ.trans f.surjective.range_eq

