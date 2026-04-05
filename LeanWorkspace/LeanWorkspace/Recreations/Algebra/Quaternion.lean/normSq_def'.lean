import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem normSq_def' : Quaternion.normSq a = a.1 ^ 2 + a.2 ^ 2 + a.3 ^ 2 + a.4 ^ 2 := by
  simp only [Quaternion.normSq_def, sq, mul_neg, sub_neg_eq_add, Quaternion.re_mul, re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
    QuaternionAlgebra.imK_star]

