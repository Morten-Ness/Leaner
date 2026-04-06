FAIL
import Mathlib

variable {M G : Type*} (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

variable [Group G] [MulSemiringAction G A] [SMulCommClass G R A]

theorem toAlgEquiv_injective [FaithfulSMul G A] :
    Function.Injective (MulSemiringAction.toAlgEquiv R A : G → A ≃ₐ[R] A) := by
  intro g h hgh
  have hsmul : ∀ a : A, g • a = h • a := fun a => DFunLike.congr_fun hgh a
  exact smul_left_injective G <| funext hsmul
