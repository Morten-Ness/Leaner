import Mathlib

variable {ι A B R : Type*} {κ : ι → Type*}

theorem Pi.spectrum_eq [CommSemiring R] [∀ i, Ring (κ i)] [∀ i, Algebra R (κ i)]
    (a : ∀ i, κ i) : spectrum R a = ⋃ i, spectrum R (a i) := by
  apply compl_injective
  simp_rw [spectrum, Set.compl_iUnion, compl_compl, resolventSet, Set.iInter_setOf,
    Pi.isUnit_iff, sub_apply, algebraMap_apply]

