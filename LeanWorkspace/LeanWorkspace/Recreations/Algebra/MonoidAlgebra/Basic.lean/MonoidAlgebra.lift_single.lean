import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Monoid M] [Monoid N] [Monoid O]

theorem lift_single (F : M →* A) (a b) : MonoidAlgebra.lift R A M F (single a b) = b • F a := by
  rw [MonoidAlgebra.lift_def, liftNC_single, Algebra.smul_def, AddMonoidHom.coe_coe]

