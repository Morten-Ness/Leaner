import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem quasispectrum.algebraMap_mem_iff (S : Type*) {R A : Type*} [Semifield R] [Field S]
    [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] {a : A} {r : R} :
    algebraMap R S r ∈ quasispectrum S a ↔ r ∈ quasispectrum R a := by
  simp_rw [Unitization.quasispectrum_eq_spectrum_inr' _ S a, spectrum.algebraMap_mem_iff]

protected alias ⟨quasispectrum.of_algebraMap_mem, quasispectrum.algebraMap_mem⟩ :=
  quasispectrum.algebraMap_mem_iff

