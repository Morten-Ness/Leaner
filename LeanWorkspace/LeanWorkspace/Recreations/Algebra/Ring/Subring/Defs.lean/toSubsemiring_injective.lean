import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

theorem toSubsemiring_injective : (toSubsemiring : Subring R → Subsemiring R).Injective := fun ⟨s, hs⟩ t ↦ by congr!

