import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem map_map (g : N →ₙ* P) (f : M →ₙ* N) : (S.map f).map g = S.map (g.comp f) := SetLike.coe_injective <| image_image _ _ _

