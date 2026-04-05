import Mathlib

variable {ι κ M M₀ R : Type*}

variable [NonUnitalNonAssocSemiring R] (l : List ι) (f : ι → R) (r : R)

theorem sum_map_mul_right : (l.map fun b ↦ f b * r).sum = (l.map f).sum * r := sum_map_hom l f <| AddMonoidHom.mulRight r

