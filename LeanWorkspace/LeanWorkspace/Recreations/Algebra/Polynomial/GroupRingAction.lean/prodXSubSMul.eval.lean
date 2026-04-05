import Mathlib

open scoped Polynomial

variable (M : Type*) [Monoid M]

variable (G : Type*) [Group G] [Fintype G]

variable (R : Type*) [CommRing R] [MulSemiringAction G R]

theorem prodXSubSMul.eval (x : R) : (prodXSubSMul G R x).eval x = 0 := letI := Classical.decEq R
  (map_prod ((Polynomial.aeval x).toRingHom.toMonoidHom : R[X] →* R) _ _).trans <|
    Finset.prod_eq_zero (Finset.mem_univ <| QuotientGroup.mk 1) <| by simp

