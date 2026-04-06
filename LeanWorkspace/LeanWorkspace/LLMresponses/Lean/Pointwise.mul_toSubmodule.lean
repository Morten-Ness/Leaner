FAIL
import Mathlib

variable {R : Type*} {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem mul_toSubmodule {R : Type*} {A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S T : Subalgebra R A) : (Subalgebra.toSubmodule S) * (Subalgebra.toSubmodule T)
        = Subalgebra.toSubmodule (S ⊔ T) := by
  rw [show (Subalgebra.toSubmodule S) * (Subalgebra.toSubmodule T) =
      Subalgebra.toSubmodule (S * T) by rfl]
  congr
  exact sup_eq_closure (A := A) S T
