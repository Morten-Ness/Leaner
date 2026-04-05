import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (A B : Subalgebra R S)

variable [Module.Free R A] [Module.Free A (Algebra.adjoin A (B : Set S))]

theorem finrank_left_dvd_finrank_sup_of_free :
    finrank R A ∣ finrank R ↥(A ⊔ B) := ⟨_, Subalgebra.finrank_sup_eq_finrank_left_mul_finrank_of_free A B⟩

