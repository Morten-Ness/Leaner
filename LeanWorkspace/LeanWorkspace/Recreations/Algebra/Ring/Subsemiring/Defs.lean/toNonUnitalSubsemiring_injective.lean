import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

theorem toNonUnitalSubsemiring_injective :
    Function.Injective (Subsemiring.toNonUnitalSubsemiring : Subsemiring R → _) := fun S₁ S₂ h => SetLike.ext'_iff.2
    (show (S₁.toNonUnitalSubsemiring : Set R) = S₂ from SetLike.ext'_iff.1 h)

