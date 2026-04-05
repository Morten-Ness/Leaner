import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem quasispectrum_eq_spectrum_inr' (R S : Type*) {A : Type*} [Semifield R]
    [Field S] [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] (a : A) :
    quasispectrum R a = spectrum R (a : Unitization S A) := by
  ext r
  have := Set.singleton_subset_iff.mpr (Unitization.zero_mem_spectrum_inr R S a)
  rw [← Set.union_eq_self_of_subset_right this, ← quasispectrum_eq_spectrum_union_zero]
  apply forall_congr' fun x ↦ ?_
  rw [not_iff_not, Units.smul_def, Units.smul_def, ← inr_smul, ← inr_neg, Unitization.isQuasiregular_inr_iff]

