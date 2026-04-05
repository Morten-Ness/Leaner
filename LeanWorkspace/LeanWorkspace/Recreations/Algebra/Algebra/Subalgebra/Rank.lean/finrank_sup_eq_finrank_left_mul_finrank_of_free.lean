import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (A B : Subalgebra R S)

variable [Module.Free R A] [Module.Free A (Algebra.adjoin A (B : Set S))]

theorem finrank_sup_eq_finrank_left_mul_finrank_of_free :
    finrank R ↥(A ⊔ B) = finrank R A * finrank A (Algebra.adjoin A (B : Set S)) := by
  simpa only [map_mul] using congr(Cardinal.toNat $(Subalgebra.rank_sup_eq_rank_left_mul_rank_of_free A B))

