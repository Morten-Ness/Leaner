import Mathlib

variable {R : Type v} [NonAssocSemiring R] [StarRing R]

theorem coe_mk (S : Subsemiring R) (h) : ((⟨S, h⟩ : StarSubsemiring R) : Set R) = S := rfl

