import Mathlib

variable {R : Type v} [NonAssocSemiring R] [StarRing R]

theorem toSubsemiring_le_iff {S₁ S₂ : StarSubsemiring R} :
    S₁.toSubsemiring ≤ S₂.toSubsemiring ↔ S₁ ≤ S₂ := Iff.rfl

