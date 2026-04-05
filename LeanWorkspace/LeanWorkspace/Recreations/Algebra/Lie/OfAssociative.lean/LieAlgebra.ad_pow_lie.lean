import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

theorem LieAlgebra.ad_pow_lie (x y z : L) (n : ℕ) :
    ((ad R L x) ^ n) ⁅y, z⁆ =
      ∑ ij ∈ antidiagonal n, n.choose ij.1 • ⁅((ad R L x) ^ ij.1) y, ((ad R L x) ^ ij.2) z⁆ := toEnd_pow_lie _ x y z n

