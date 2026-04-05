import Mathlib

variable {A B F : Type*} [Semiring A] [Semiring B]

theorem MulEquiv.isField (hB : IsField B) (e : A ≃* B) : IsField A := IsLocalHom.isField e.injective hB

