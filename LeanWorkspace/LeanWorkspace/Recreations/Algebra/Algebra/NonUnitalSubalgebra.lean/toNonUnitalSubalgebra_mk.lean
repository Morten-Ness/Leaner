import Mathlib

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

theorem toNonUnitalSubalgebra_mk (p : Submodule R A) hmul :
    p.toNonUnitalSubalgebra hmul =
      NonUnitalSubalgebra.mk ⟨⟨⟨p, p.add_mem⟩, p.zero_mem⟩, hmul _ _⟩ p.smul_mem' := rfl

