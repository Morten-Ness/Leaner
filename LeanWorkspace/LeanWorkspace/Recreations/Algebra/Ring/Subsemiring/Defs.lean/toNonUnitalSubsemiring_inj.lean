import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

theorem toNonUnitalSubsemiring_inj {S₁ S₂ : Subsemiring R} :
    S₁.toNonUnitalSubsemiring = S₂.toNonUnitalSubsemiring ↔ S₁ = S₂ := Subsemiring.toNonUnitalSubsemiring_injective.eq_iff

