import Mathlib

variable (R : Type*) [CommRing R]

theorem toSubsemiring_inj {P₁ P₂ : RingPreordering R} :
    P₁.toSubsemiring = P₂.toSubsemiring ↔ P₁ = P₂ := RingPreordering.toSubsemiring_injective.eq_iff

