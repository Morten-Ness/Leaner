import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem quasispectrum_eq_spectrum_union (R : Type*) {A : Type*} [CommSemiring R]
    [Ring A] [Algebra R A] (a : A) : quasispectrum R a = spectrum R a ∪ {r : R | ¬ IsUnit r} := by
  ext r
  rw [quasispectrum]
  simp only [Set.mem_setOf_eq, Set.mem_union, ← imp_iff_or_not, spectrum.mem_iff]
  congr! 1 with hr
  rw [not_iff_not, isQuasiregular_iff_isUnit, ← sub_eq_add_neg, Algebra.algebraMap_eq_smul_one]
  exact (IsUnit.smul_sub_iff_sub_inv_smul hr.unit a).symm

