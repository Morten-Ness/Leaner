import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

variable (r : R → R → Prop)

theorem mkRingHom_surjective (r : R → R → Prop) : Function.Surjective (mkRingHom r) := by
  simp only [mkRingHom_def, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  rintro ⟨⟨⟩⟩
  simp

