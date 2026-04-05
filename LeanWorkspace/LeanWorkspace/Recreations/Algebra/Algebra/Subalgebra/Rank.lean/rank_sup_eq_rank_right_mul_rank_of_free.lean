import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (A B : Subalgebra R S)

variable [Module.Free R B] [Module.Free B (Algebra.adjoin B (A : Set S))]

theorem rank_sup_eq_rank_right_mul_rank_of_free :
    Module.rank R ↥(A ⊔ B) = Module.rank R B * Module.rank B (Algebra.adjoin B (A : Set S)) := by
  rw [sup_comm, Subalgebra.rank_sup_eq_rank_left_mul_rank_of_free]

