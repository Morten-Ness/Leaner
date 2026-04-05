import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

theorem mk_le_mk {S S' : Subsemiring R} (h₁ h₂) :
    (⟨S, h₁⟩ : Subring R) ≤ (⟨S', h₂⟩ : Subring R) ↔ S ≤ S' := Iff.rfl

