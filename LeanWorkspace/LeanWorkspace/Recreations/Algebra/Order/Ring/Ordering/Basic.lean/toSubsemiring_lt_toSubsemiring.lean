import Mathlib

variable {R : Type*} [CommRing R] {P : RingPreordering R}

theorem toSubsemiring_lt_toSubsemiring {P₁ P₂ : RingPreordering R} :
    P₁.toSubsemiring < P₂.toSubsemiring ↔ P₁ < P₂ := .rfl

