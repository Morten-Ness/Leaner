import Mathlib

variable {ι κ M M₀ R : Type*}

variable [NonUnitalNonAssocSemiring R] (l : List ι) (f : ι → R) (r : R)

theorem sum_map_mul_left : (l.map fun b ↦ r * f b).sum = r * (l.map f).sum := sum_map_hom l f <| AddMonoidHom.mulLeft r

