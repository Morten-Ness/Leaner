import Mathlib

variable {X G : Type*} {A B C : Set X}

variable [SMul G X]

theorem restr_of_source_subset {f : Equidecomp X G} {A : Set X} (hA : f.source ⊆ A) :
    f.restr A = f := by
  apply Equidecomp.toPartialEquiv_injective
  rw [Equidecomp.toPartialEquiv_restr, PartialEquiv.restr_eq_of_source_subset hA]

