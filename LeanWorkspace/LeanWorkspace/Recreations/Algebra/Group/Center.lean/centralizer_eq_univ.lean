import Mathlib

variable {M : Type*} {S T : Set M}

variable [CommSemigroup M]

theorem centralizer_eq_univ : Set.centralizer S = univ := eq_univ_of_forall fun _ _ _ ↦ mul_comm _ _

