FAIL
import Mathlib

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A]

variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem commute_of_mem_adjoin_self {a b : A} (hb : b ∈ NonUnitalAlgebra.adjoin R {a}) :
    Commute a b := by
  let S : NonUnitalSubalgebra R A := { x | Commute a x }
  have haS : a ∈ S := by
    exact Commute.refl a
  have hS : NonUnitalAlgebra.adjoin R {a} ≤ S := by
    exact NonUnitalAlgebra.adjoin_le fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact haS
  exact hS hb
