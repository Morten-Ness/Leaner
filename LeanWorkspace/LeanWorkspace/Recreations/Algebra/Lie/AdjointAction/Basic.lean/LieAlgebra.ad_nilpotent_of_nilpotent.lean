import Mathlib

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem LieAlgebra.ad_nilpotent_of_nilpotent {a : A} (h : IsNilpotent a) :
    IsNilpotent (LieAlgebra.ad R A a) := by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  have hl : IsNilpotent (LinearMap.mulLeft R a) := by rwa [LinearMap.isNilpotent_mulLeft_iff]
  have hr : IsNilpotent (LinearMap.mulRight R a) := by rwa [LinearMap.isNilpotent_mulRight_iff]
  exact (LinearMap.commute_mulLeft_right a a).isNilpotent_sub hl hr

