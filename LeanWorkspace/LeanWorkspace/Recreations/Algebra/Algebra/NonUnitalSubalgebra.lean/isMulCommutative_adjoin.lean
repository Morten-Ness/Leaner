import Mathlib

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A]

variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem isMulCommutative_adjoin {s : Set A} (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) :
    IsMulCommutative (NonUnitalAlgebra.adjoin R s) := have := NonUnitalAlgebra.adjoin_le_centralizer_centralizer R s
  .of_setLike_mul_comm fun _ h₁ _ h₂ ↦
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

