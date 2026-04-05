import Mathlib

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A]

variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem commute_of_mem_adjoin_of_forall_mem_commute {a b : A} {s : Set A}
    (hb : b ∈ NonUnitalAlgebra.adjoin R s) (h : ∀ b ∈ s, Commute a b) :
    Commute a b := by
  have : a ∈ NonUnitalSubalgebra.centralizer R s := by simpa only [Commute.symm_iff (a := a)] using h
  exact NonUnitalAlgebra.adjoin_le_centralizer_centralizer R s hb a this

