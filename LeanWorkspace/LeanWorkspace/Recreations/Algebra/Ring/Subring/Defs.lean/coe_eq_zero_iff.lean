import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable (s : Subring R)

theorem coe_eq_zero_iff {x : s} : (x : R) = 0 ↔ x = 0 := ⟨fun h => Subtype.ext (Trans.trans h Subring.coe_zero s.symm), fun h => h.symm ▸ Subring.coe_zero s⟩

