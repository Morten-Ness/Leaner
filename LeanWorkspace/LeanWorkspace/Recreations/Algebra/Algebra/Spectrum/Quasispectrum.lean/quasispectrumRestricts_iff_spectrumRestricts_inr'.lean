import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem quasispectrumRestricts_iff_spectrumRestricts_inr'
    {R S' A : Type*} (S : Type*) [Semifield R] [Semifield S'] [Field S] [NonUnitalRing A]
    [Module R A] [Module S' A] [Module S A] [IsScalarTower S A A] [SMulCommClass S A A]
    [Algebra R S'] [Algebra S' S] [Algebra R S] [IsScalarTower S' S A] [IsScalarTower R S A]
    {a : A} {f : S' → R} :
    QuasispectrumRestricts a f ↔ SpectrumRestricts (a : Unitization S A) f := by
  simp only [quasispectrumRestricts_iff, SpectrumRestricts, Unitization.quasispectrum_inr_eq]

