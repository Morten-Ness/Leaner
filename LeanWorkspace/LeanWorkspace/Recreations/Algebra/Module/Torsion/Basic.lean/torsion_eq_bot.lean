import Mathlib

variable {R M : Type*}

variable [CommRing R] [AddCommGroup M] [Module R M]

theorem torsion_eq_bot : torsion R (M ⧸ torsion R M) = ⊥ := eq_bot_iff.mpr fun z =>
    Quotient.inductionOn' z fun x ⟨a, hax⟩ => by
      rw [Quotient.mk''_eq_mk, ← Quotient.mk_smul, Quotient.mk_eq_zero] at hax
      rw [mem_bot, Quotient.mk''_eq_mk, Quotient.mk_eq_zero]
      obtain ⟨b, h⟩ := hax
      exact ⟨b * a, (mul_smul _ _ _).trans h⟩

