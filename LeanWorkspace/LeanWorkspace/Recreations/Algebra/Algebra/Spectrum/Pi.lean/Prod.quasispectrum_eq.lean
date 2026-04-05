import Mathlib

variable {ι A B R : Type*} {κ : ι → Type*}

theorem Prod.quasispectrum_eq [CommSemiring R] [NonUnitalRing A] [NonUnitalRing B]
    [Module R A] [Module R B] (a : A) (b : B) :
    quasispectrum R (⟨a, b⟩ : A × B) = quasispectrum R a ∪ quasispectrum R b := by
  apply compl_injective
  ext r
  simp only [quasispectrum, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_not, Set.mem_union]
  by_cases hr : IsUnit r
  · lift r to Rˣ using hr with r' hr'
    simp [isQuasiregular_prod_iff]
  · simp [hr]

