import Mathlib

variable (M : Type*) [Monoid M]

variable (G : Type*) [Group G] [Fintype G]

variable (R : Type*) [CommRing R] [MulSemiringAction G R]

theorem prodXSubSMul.coeff (x : R) (g : G) (n : ℕ) :
    g • (prodXSubSMul G R x).coeff n = (prodXSubSMul G R x).coeff n := by
  rw [← Polynomial.coeff_smul, prodXSubSMul.smul]

