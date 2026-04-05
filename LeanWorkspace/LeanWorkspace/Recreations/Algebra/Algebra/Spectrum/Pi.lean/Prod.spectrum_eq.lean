import Mathlib

variable {ι A B R : Type*} {κ : ι → Type*}

theorem Prod.spectrum_eq [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (a : A) (b : B) : spectrum R (⟨a, b⟩ : A × B) = spectrum R a ∪ spectrum R b := by
  apply compl_injective
  simp_rw [spectrum, Set.compl_union, compl_compl, resolventSet, ← Set.setOf_and,
    Prod.isUnit_iff, algebraMap_apply, mk_sub_mk]

