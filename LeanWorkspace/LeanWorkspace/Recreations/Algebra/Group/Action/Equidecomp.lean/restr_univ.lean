import Mathlib

variable {X G : Type*} {A B C : Set X}

variable [SMul G X]

theorem restr_univ (f : Equidecomp X G) : f.restr Set.univ = f := Equidecomp.restr_of_source_subset <| subset_univ _

