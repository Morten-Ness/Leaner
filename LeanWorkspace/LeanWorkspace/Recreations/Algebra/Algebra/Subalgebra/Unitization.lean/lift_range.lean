import Mathlib

variable {R A C : Type*} [CommSemiring R] [NonUnitalSemiring A]

variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] [Semiring C] [Algebra R C]

theorem lift_range (f : A →ₙₐ[R] C) :
    (lift f).range = Algebra.adjoin R (NonUnitalAlgHom.range f : Set C) := eq_of_forall_ge_iff fun c ↦ by rw [Unitization.lift_range_le, Algebra.adjoin_le_iff]; rfl

