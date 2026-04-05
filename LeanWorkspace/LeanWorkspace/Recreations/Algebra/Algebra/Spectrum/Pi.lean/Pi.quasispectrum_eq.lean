import Mathlib

variable {ι A B R : Type*} {κ : ι → Type*}

theorem Pi.quasispectrum_eq [Nonempty ι] [CommSemiring R] [∀ i, NonUnitalRing (κ i)]
    [∀ i, Module R (κ i)] (a : ∀ i, κ i) :
    quasispectrum R a = ⋃ i, quasispectrum R (a i) := by
  ext r
  simp only [quasispectrum, Set.mem_setOf_eq, Set.mem_iUnion]
  by_cases hr : IsUnit r
  · lift r to Rˣ using hr with r' hr'
    simp [isQuasiregular_pi_iff]
  · simp [hr]

