import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (A B : Subalgebra R S)

variable [Module.Free R B] [Module.Free B (Algebra.adjoin B (A : Set S))]

theorem finrank_sup_eq_finrank_right_mul_finrank_of_free :
    finrank R ↥(A ⊔ B) = finrank R B * finrank B (Algebra.adjoin B (A : Set S)) := by
  rw [sup_comm, Subalgebra.finrank_sup_eq_finrank_left_mul_finrank_of_free]

