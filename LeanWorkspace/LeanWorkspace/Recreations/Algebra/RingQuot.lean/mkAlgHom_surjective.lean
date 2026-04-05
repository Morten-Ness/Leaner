import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

variable (r : R → R → Prop)

variable [Semiring T]

theorem mkAlgHom_surjective (s : A → A → Prop) : Function.Surjective (mkAlgHom S s) := by
  suffices Function.Surjective fun x ↦ (⟨.mk (Rel s) x⟩ : RingQuot s) by
    simpa [mkAlgHom_def, mkRingHom_def]
  rintro ⟨⟨a⟩⟩
  use a

