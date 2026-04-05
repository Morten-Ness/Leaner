import Mathlib

variable (A : Type*)

variable {A} [NonUnitalNonAssocCommRing A]

theorem two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add [IsCommJordan A] (a b : A) :
    2 • (⁅L a, L (a * b)⁆ + ⁅L b, L (b * a)⁆) = ⁅L (a * a), L b⁆ + ⁅L (b * b), L a⁆ := by
  suffices 2 • ⁅L a, L (a * b)⁆ + 2 • ⁅L b, L (b * a)⁆ + ⁅L b, L (a * a)⁆ + ⁅L a, L (b * b)⁆ = 0 by
    rwa [← sub_eq_zero, ← sub_sub, sub_eq_add_neg, sub_eq_add_neg, lie_skew, lie_skew, nsmul_add]
  convert (commute_lmul_lmul_sq (a + b)).lie_eq using 1
  simp only [add_mul, mul_add, map_add, lie_add, add_lie, mul_comm b a,
    (commute_lmul_lmul_sq a).lie_eq, (commute_lmul_lmul_sq b).lie_eq, zero_add, add_zero, two_smul]
  abel

-- Porting note: the monolithic `calc`-based proof of `two_nsmul_lie_lmul_lmul_add_add_eq_zero`
-- has had four auxiliary parts `aux{0,1,2,3}` split off from it.

