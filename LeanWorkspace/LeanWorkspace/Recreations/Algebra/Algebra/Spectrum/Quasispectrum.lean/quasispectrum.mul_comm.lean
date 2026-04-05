import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem quasispectrum.mul_comm {R A : Type*} [CommRing R] [NonUnitalRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] (a b : A) :
    quasispectrum R (a * b) = quasispectrum R (b * a) := by
  rw [← Set.inter_union_compl (quasispectrum R (a * b)) {r | IsUnit r},
    ← Set.inter_union_compl (quasispectrum R (b * a)) {r | IsUnit r}]
  congr! 1
  · simpa [Set.inter_comm _ {r | IsUnit r}, Unitization.quasispectrum_eq_spectrum_inr,
      Unitization.inr_mul] using spectrum.setOf_isUnit_inter_mul_comm _ _
  · rw [Set.inter_eq_right.mpr, Set.inter_eq_right.mpr]
    all_goals exact fun _ ↦ quasispectrum.not_isUnit_mem _

