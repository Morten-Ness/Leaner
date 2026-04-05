import Mathlib

variable {R A : Type*}

theorem RingHom.charP_iff_charP {K L : Type*} [DivisionRing K] [NonAssocSemiring L] [Nontrivial L]
    (f : K →+* L) (p : ℕ) : CharP K p ↔ CharP L p := by
  simp only [charP_iff, ← f.injective.eq_iff, map_natCast f, map_zero f]

