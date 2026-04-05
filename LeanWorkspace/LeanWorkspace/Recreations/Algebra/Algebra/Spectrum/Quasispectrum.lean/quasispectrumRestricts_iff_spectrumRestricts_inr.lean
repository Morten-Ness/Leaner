import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem quasispectrumRestricts_iff_spectrumRestricts_inr (S : Type*) {R A : Type*} [Semifield R]
    [Field S] [NonUnitalRing A] [Algebra R S] [Module R A] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [IsScalarTower R S A] {a : A} {f : S → R} :
    QuasispectrumRestricts a f ↔ SpectrumRestricts (a : Unitization S A) f := by
  rw [quasispectrumRestricts_iff, spectrumRestricts_iff,
    ← Unitization.quasispectrum_eq_spectrum_inr']

