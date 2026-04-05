import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem normSq_add (a b : ℍ[R]) : Quaternion.normSq (a + b) = Quaternion.normSq a + Quaternion.normSq b + 2 * (a * star b).re := calc
    Quaternion.normSq (a + b) = Quaternion.normSq a + (a * star b).re + ((b * star a).re + Quaternion.normSq b) := by
      simp_rw [Quaternion.normSq_def, star_add, add_mul, mul_add, re_add]
    _ = Quaternion.normSq a + Quaternion.normSq b + ((a * star b).re + (b * star a).re) := by abel
    _ = Quaternion.normSq a + Quaternion.normSq b + 2 * (a * star b).re := by
      rw [← re_add, ← star_mul_star a b, Quaternion.self_add_star', Quaternion.re_coe]

