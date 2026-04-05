import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (A B : Subalgebra R S)

variable [Module.Free R B] [Module.Free B (Algebra.adjoin B (A : Set S))]

theorem finrank_right_dvd_finrank_sup_of_free :
    finrank R B ∣ finrank R ↥(A ⊔ B) := ⟨_, Subalgebra.finrank_sup_eq_finrank_right_mul_finrank_of_free A B⟩

