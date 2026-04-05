import Mathlib

variable {R : Type*} [CommSemiring R]

variable {A : Type*} [Semiring A] [Algebra R A]

theorem centralizer_coe_sup (S T : Subalgebra R A) :
    centralizer R ((S ⊔ T : Subalgebra R A) : Set A) = centralizer R S ⊓ centralizer R T := eq_of_forall_le_iff fun K ↦ by
    simp_rw [Subalgebra.le_centralizer_iff, sup_le_iff, le_inf_iff, K.le_centralizer_iff]

