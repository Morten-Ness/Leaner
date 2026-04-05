import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

variable (r : R → R → Prop)

variable [Semiring T]

theorem mkAlgHom_coe (s : A → A → Prop) : (mkAlgHom S s : A →+* RingQuot s) = mkRingHom s := by
  simp_rw [mkAlgHom_def, mkRingHom_def]
  rfl

