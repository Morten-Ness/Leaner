import Mathlib

section

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

end

section

variable {ι A B R : Type*} {κ : ι → Type*}

theorem Pi.spectrum_eq [CommSemiring R] [∀ i, Ring (κ i)] [∀ i, Algebra R (κ i)]
    (a : ∀ i, κ i) : spectrum R a = ⋃ i, spectrum R (a i) := by
  apply compl_injective
  simp_rw [spectrum, Set.compl_iUnion, compl_compl, resolventSet, Set.iInter_setOf,
    Pi.isUnit_iff, sub_apply, algebraMap_apply]

end

section

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

end

section

variable {ι A B R : Type*} {κ : ι → Type*}

theorem Prod.spectrum_eq [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (a : A) (b : B) : spectrum R (⟨a, b⟩ : A × B) = spectrum R a ∪ spectrum R b := by
  apply compl_injective
  simp_rw [spectrum, Set.compl_union, compl_compl, resolventSet, ← Set.setOf_and,
    Prod.isUnit_iff, algebraMap_apply, mk_sub_mk]

end

section

variable {ι A B R : Type*} {κ : ι → Type*}

theorem isQuasiregular_pi_iff [∀ i, NonUnitalSemiring (κ i)] (x : ∀ i, κ i) :
    IsQuasiregular x ↔ ∀ i, IsQuasiregular (x i) := by
  simp only [isQuasiregular_iff', ← isUnit_map_iff (PreQuasiregular.toPi κ), Pi.isUnit_iff]
  congr!

end

section

variable {ι A B R : Type*} {κ : ι → Type*}

theorem isQuasiregular_prod_iff [NonUnitalSemiring A] [NonUnitalSemiring B] (a : A) (b : B) :
    IsQuasiregular (⟨a, b⟩ : A × B) ↔ IsQuasiregular a ∧ IsQuasiregular b := by
  simp only [isQuasiregular_iff', ← isUnit_map_iff (PreQuasiregular.toProd A B), Prod.isUnit_iff]
  congr!

end
