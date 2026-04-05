import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

variable {S : Submonoid M} [Fintype S]

theorem card_le_one_iff_eq_bot : card S ≤ 1 ↔ S = ⊥ := ⟨fun h =>
    (eq_bot_iff_forall _).2 fun x hx => by
      simpa [Subtype.ext_iff] using card_le_one_iff.1 h ⟨x, hx⟩ 1,
    fun h => by simp [h]⟩

