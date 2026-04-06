FAIL
import Mathlib

variable {X G : Type*} {A B C : Set X}

variable [SMul G X]

theorem restr_of_source_subset {f : Equidecomp X G} {A : Set X} (hA : f.source ⊆ A) :
    f.restr A = f := by
  cases f with
  | mk toPartialEquiv isDecompOn' =>
      change toPartialEquiv.restr A = toPartialEquiv
      exact PartialEquiv.restr_eq_self.2 hA
