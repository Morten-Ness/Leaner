import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem quasispectrum_eq_spectrum_inr (R : Type*) {A : Type*} [CommRing R] [NonUnitalRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] (a : A) :
    quasispectrum R a = spectrum R (a : Unitization R A) := by
  ext r
  have : { r | ¬ IsUnit r} ⊆ spectrum R _ := Unitization.mem_spectrum_inr_of_not_isUnit a
  rw [← Set.union_eq_left.mpr this, ← quasispectrum_eq_spectrum_union]
  apply forall_congr' fun hr ↦ ?_
  rw [not_iff_not, Units.smul_def, Units.smul_def, ← inr_smul, ← inr_neg, Unitization.isQuasiregular_inr_iff]

