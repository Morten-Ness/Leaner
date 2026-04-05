import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem subset_singleton_zero_compl {a : A} (ha : IsUnit a) : spectrum R a ⊆ {0}ᶜ := Set.subset_compl_singleton_iff.mpr <| spectrum.zero_notMem R ha

