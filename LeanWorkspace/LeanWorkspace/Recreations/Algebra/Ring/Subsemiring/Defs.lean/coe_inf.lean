import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

theorem coe_inf (p p' : Subsemiring R) : ((p ⊓ p' : Subsemiring R) : Set R) = (p : Set R) ∩ p' := rfl

