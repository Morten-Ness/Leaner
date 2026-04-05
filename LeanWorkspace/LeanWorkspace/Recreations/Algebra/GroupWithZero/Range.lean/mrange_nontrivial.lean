import Mathlib

variable {G H : Type*} [MulZeroOneClass G] [MulZeroOneClass H] [Nontrivial H] (f : G →*₀ H)

theorem mrange_nontrivial :
    Nontrivial (MonoidHom.mrange f) := ⟨1, 0, by simp [Subtype.ext_iff]⟩

